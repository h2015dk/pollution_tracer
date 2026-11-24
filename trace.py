#!/usr/bin/env python3
"""全方位污染源溯源資料收集程式

輸入 經緯度 + 時間，蒐集半徑 N 公里內：
  1. 固定排放源（工廠/煙囪/儲槽/電廠/加油站/砂石場/廢棄物設施…，來源 OpenStreetMap）
  2. 熱異常/火點（NASA FIRMS VIIRS，需 FIRMS_MAP_KEY）
  3. 氣象（Open-Meteo 風向風速）→ 判斷各污染源是否位於「上風處」
  4. 事件線索（火災/繞境/廟會/煙火/焚燒/道路施工/空污 新聞，Google News RSS）
  5. 使用者自備固定源清單（CSV: name,lat,lon,category,note）
並彙整成單一互動式地圖 (map.html)。
"""
import argparse
import csv
import html
import json
import math
import os
import sys
import time
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path
from urllib.parse import quote

import folium
import requests
from folium.plugins import MarkerCluster

TZ = timezone(timedelta(hours=8))  # Asia/Taipei
UA = {"User-Agent": "pollution-source-tracer/1.0 (environmental research)"}
OVERPASS = [
    "https://overpass-api.de/api/interpreter",
    "https://overpass.kumi.systems/api/interpreter",
]

# 類別 -> (Overpass 篩選條件, 地圖顏色)
OSM_CATEGORIES = {
    "工業區/工廠": (['way["landuse"="industrial"]', 'nwr["man_made"="works"]'], "#d62728"),
    "煙囪/儲槽/燃燒塔": (['nwr["man_made"="chimney"]', 'nwr["man_made"="storage_tank"]',
                       'nwr["man_made"="flare"]'], "#8c564b"),
    "電廠/發電設施": (['nwr["power"="plant"]',
                    'nwr["power"="generator"]["generator:source"~"coal|gas|oil|waste|biomass"]'], "#9467bd"),
    "廢棄物/掩埋/污水處理": (['nwr["landuse"="landfill"]', 'nwr["amenity"="waste_transfer_station"]',
                         'nwr["man_made"="wastewater_plant"]'], "#7f7f7f"),
    "砂石/採礦/混凝土": (['nwr["landuse"="quarry"]', 'nwr["industrial"="concrete_plant"]'], "#bcbd22"),
    "加油站(VOC)": (['nwr["amenity"="fuel"]'], "#17becf"),
    "殯葬/火化": (['nwr["amenity"="crematorium"]'], "#e377c2"),
    "廟宇(香燭/金爐/鞭炮/繞境)": (['nwr["amenity"="place_of_worship"]["religion"~"taoist|buddhist|folk"]'], "#ff7f0e"),
    "道路/工地施工": (['way["highway"="construction"]', 'nwr["landuse"="construction"]'], "#2ca02c"),
}
CLUSTER_CATS = {"加油站(VOC)", "廟宇(香燭/金爐/鞭炮/繞境)"}
FIRMS_SATS = ["VIIRS_SNPP", "VIIRS_NOAA20", "VIIRS_NOAA21"]
HEAT_CATS = {"工業區/工廠", "煙囪/儲槽/燃燒塔", "電廠/發電設施", "自備固定源"}  # 會持續發熱、易被誤判成火點
# 台灣範圍（概略框：本島+離島、澎湖、馬祖、金門）(lat_min, lat_max, lon_min, lon_max)
TAIWAN_BOXES = [(21.8, 25.4, 120.0, 122.1), (23.1, 23.85, 119.3, 119.75),
                (25.9, 26.4, 119.9, 120.6), (24.3, 24.6, 118.15, 118.6)]
NEWS_KEYWORDS = ["火災", "繞境", "廟會", "煙火", "焚燒", "道路施工", "空污", "工廠 異味"]


# ---------------------------------------------------------------- 幾何
def haversine(lat1, lon1, lat2, lon2):
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dl = math.radians(lon2 - lon1)
    a = math.sin((p2 - p1) / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * 6371.0088 * math.asin(math.sqrt(a))


def bearing(lat1, lon1, lat2, lon2):
    """從 (lat1,lon1) 看向 (lat2,lon2) 的方位角，0=北，順時針。"""
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dl = math.radians(lon2 - lon1)
    y = math.sin(dl) * math.cos(p2)
    x = math.cos(p1) * math.sin(p2) - math.sin(p1) * math.cos(p2) * math.cos(dl)
    return (math.degrees(math.atan2(y, x)) + 360) % 360


def angdiff(a, b):
    d = abs(a - b) % 360
    return min(d, 360 - d)


def destination(lat, lon, brg, km):
    d = km / 6371.0088
    b, p1, l1 = math.radians(brg), math.radians(lat), math.radians(lon)
    p2 = math.asin(math.sin(p1) * math.cos(d) + math.cos(p1) * math.sin(d) * math.cos(b))
    l2 = l1 + math.atan2(math.sin(b) * math.sin(d) * math.cos(p1), math.cos(d) - math.sin(p1) * math.sin(p2))
    return math.degrees(p2), math.degrees(l2)


def compass(deg):
    names = ["北", "東北", "東", "東南", "南", "西南", "西", "西北"]
    return names[int((deg + 22.5) // 45) % 8]


# ---------------------------------------------------------------- 蒐集器
def collect_osm(lat, lon, radius_km):
    out = []
    for cat, (filters, _) in OSM_CATEGORIES.items():
        parts = "".join(f"{f}(around:{int(radius_km * 1000)},{lat},{lon});" for f in filters)
        query = f"[out:json][timeout:90];({parts});out center tags;"
        data = None
        for url in OVERPASS:
            try:
                r = requests.post(url, data={"data": query}, headers=UA, timeout=120)
                r.raise_for_status()
                data = r.json()
                break
            except Exception as e:  # 換下一個鏡像
                print(f"  [overpass] {cat} @ {url}: {e}", file=sys.stderr)
        if data is None:
            continue
        for el in data.get("elements", []):
            tags = el.get("tags", {})
            la = el.get("lat") or el.get("center", {}).get("lat")
            lo = el.get("lon") or el.get("center", {}).get("lon")
            if la is None or lo is None:
                continue
            name = tags.get("name:zh") or tags.get("name") or tags.get("operator") or "(未命名)"
            out.append(dict(name=name, category=cat, lat=la, lon=lo, source="OSM",
                            note=f"osm:{el['type']}/{el['id']}"))
        time.sleep(2)  # 對 Overpass 客氣一點
    return out


def collect_extra(path):
    if not path or not Path(path).exists():
        return []
    out = []
    with open(path, encoding="utf-8-sig") as f:
        for row in csv.DictReader(f):
            try:
                out.append(dict(name=row.get("name", "(未命名)"), category=row.get("category") or "自備固定源",
                                lat=float(row["lat"]), lon=float(row["lon"]), source="使用者CSV",
                                note=row.get("note", "")))
            except (KeyError, ValueError):
                continue
    return out


def collect_wind(lat, lon, t):
    """回傳 t 前 3 小時的向量平均風（風向=風吹來的方向）。"""
    age = (datetime.now(TZ) - t).days
    url = ("https://archive-api.open-meteo.com/v1/archive" if age > 5
           else "https://api.open-meteo.com/v1/forecast")
    params = dict(latitude=lat, longitude=lon, timezone="Asia/Taipei", wind_speed_unit="ms",
                  start_date=(t - timedelta(days=1)).date().isoformat(), end_date=t.date().isoformat(),
                  hourly="wind_speed_10m,wind_direction_10m,temperature_2m,precipitation")
    r = requests.get(url, params=params, headers=UA, timeout=30)
    r.raise_for_status()
    h = r.json()["hourly"]
    xs = ys = ws_sum = prec = 0.0
    n = 0
    for ts, ws, wd, pr in zip(h["time"], h["wind_speed_10m"], h["wind_direction_10m"], h["precipitation"]):
        dt = datetime.fromisoformat(ts).replace(tzinfo=TZ)
        if t - timedelta(hours=3) < dt <= t + timedelta(hours=1) and ws is not None and wd is not None:
            xs += ws * math.sin(math.radians(wd))
            ys += ws * math.cos(math.radians(wd))
            ws_sum += ws
            prec += pr or 0
            n += 1
    if n == 0:
        raise RuntimeError("氣象資料不足")
    return dict(dir=(math.degrees(math.atan2(xs, ys)) + 360) % 360, speed=ws_sum / n, precip=prec, hours=n)


def in_taiwan(lat, lon):
    return any(a <= lat <= b and c <= lon <= d for a, b, c, d in TAIWAN_BOXES)


def collect_fires(lat, lon, radius_km, t0, t1, key):
    """同時查 SNPP / NOAA-20 / NOAA-21 三顆 VIIRS，增加過境次數。"""
    if not key:
        print("  [firms] 未設定 FIRMS_MAP_KEY，略過火點", file=sys.stderr)
        return []
    dlat = radius_km / 111.0
    dlon = radius_km / (111.0 * math.cos(math.radians(lat)))
    area = f"{lon - dlon:.4f},{lat - dlat:.4f},{lon + dlon:.4f},{lat + dlat:.4f}"
    u0, u1 = t0.astimezone(timezone.utc), t1.astimezone(timezone.utc)
    suffix = "NRT" if (datetime.now(timezone.utc) - u1).days < 60 else "SP"
    days = min((u1.date() - u0.date()).days + 1, 5)
    out = []
    for sat in FIRMS_SATS:
        src = f"{sat}_{suffix}"
        url = (f"https://firms.modaps.eosdis.nasa.gov/api/area/csv/{key}/{src}/{area}/"
               f"{days}/{u0.date().isoformat()}")
        try:
            r = requests.get(url, headers=UA, timeout=60)
            r.raise_for_status()
            if not r.text.startswith("latitude"):
                raise RuntimeError(r.text[:120])
        except Exception as e:  # 某顆衛星無資料不影響其他
            print(f"  [firms] {src}: {e}", file=sys.stderr)
            continue
        for row in csv.DictReader(r.text.splitlines()):
            la, lo = float(row["latitude"]), float(row["longitude"])
            acq = datetime.strptime(row["acq_date"] + row["acq_time"].zfill(4), "%Y-%m-%d%H%M").replace(
                tzinfo=timezone.utc)
            if u0 <= acq <= u1 and haversine(lat, lon, la, lo) <= radius_km:
                out.append(dict(lat=la, lon=lo, time=acq.astimezone(TZ).isoformat(timespec="minutes"),
                                confidence=row.get("confidence", ""), frp=row.get("frp", ""), product=src))
    return sorted(out, key=lambda f: f["time"])


def flag_industrial_fires(fires, sources, buffer_km):
    """火點落在已知工業熱源 buffer_km 內 → 標為疑似工業熱源（啟發式；面狀工業區以中心點計算）。"""
    heat = [s for s in sources if s["category"] in HEAT_CATS]
    for f in fires:
        best = min(((haversine(f["lat"], f["lon"], s["lat"], s["lon"]), s) for s in heat),
                   key=lambda x: x[0], default=None)
        ok = best is not None and best[0] <= buffer_km
        f["industrial"] = ok
        f["near_source"] = best[1]["name"] if ok else ""
        f["near_km"] = round(best[0], 3) if ok else ""
    return fires


def reverse_geocode(lat, lon):
    r = requests.get("https://nominatim.openstreetmap.org/reverse", headers=UA, timeout=30,
                     params=dict(lat=lat, lon=lon, format="jsonv2", zoom=14, **{"accept-language": "zh-TW"}))
    ad = r.json().get("address", {})
    district = next((ad[k] for k in ("suburb", "city_district", "town", "village") if k in ad), None)
    city = ad.get("city") or ad.get("county") or ad.get("state")
    return [n for n in dict.fromkeys([district, city]) if n]


def collect_news(places, t0, t1):
    items = {}
    for name in places:
        for kw in NEWS_KEYWORDS:
            url = (f"https://news.google.com/rss/search?q={quote(f'{name} {kw}')}"
                   "&hl=zh-TW&gl=TW&ceid=TW:zh-Hant")
            try:
                r = requests.get(url, headers=UA, timeout=30)
                root = ET.fromstring(r.content)
            except Exception as e:
                print(f"  [news] {name} {kw}: {e}", file=sys.stderr)
                continue
            for it in root.iter("item"):
                try:
                    dt = parsedate_to_datetime(it.findtext("pubDate")).astimezone(TZ)
                except Exception:
                    continue
                if t0 - timedelta(days=1) <= dt <= t1 + timedelta(days=1):
                    link = it.findtext("link")
                    items.setdefault(link, dict(title=it.findtext("title"), link=link,
                                                published=dt.isoformat(timespec="minutes"),
                                                media=it.findtext("source") or "", keyword=kw, place=name))
            time.sleep(1)
    return sorted(items.values(), key=lambda x: x["published"], reverse=True)


# ---------------------------------------------------------------- 地圖
def build_map(lat, lon, radius, t, wind, sources, fires, news, places, out_dir):
    m = folium.Map(location=[lat, lon], zoom_start=12, tiles="OpenStreetMap")
    folium.Circle([lat, lon], radius=radius * 1000, color="#1f77b4", fill=False, weight=2,
                  tooltip=f"{radius:g} km").add_to(m)
    folium.Circle([lat, lon], radius=radius * 500, color="#1f77b4", fill=False, weight=1,
                  dash_array="6").add_to(m)
    folium.Marker([lat, lon], tooltip="監測點", popup=f"{lat:.5f}, {lon:.5f}<br>{t:%Y-%m-%d %H:%M}",
                  icon=folium.Icon(color="blue", icon="crosshairs", prefix="fa")).add_to(m)

    if wind:
        pts = [[lat, lon]] + [list(destination(lat, lon, b, radius)) for b in range(int(wind["dir"]) - 45,
                                                                                    int(wind["dir"]) + 46, 5)]
        folium.Polygon(pts, color="#ff7f0e", weight=1, fill=True, fill_opacity=0.12,
                       tooltip=f"上風處扇區（風自{compass(wind['dir'])}方 {wind['dir']:.0f}° 吹來）").add_to(m)

    groups = {}
    colors = {c: v[1] for c, v in OSM_CATEGORIES.items()}
    for s in sorted(sources, key=lambda x: x["dist_km"]):
        cat = s["category"]
        if cat not in groups:
            fg = folium.FeatureGroup(name=f"{cat}", show=cat not in CLUSTER_CATS or True)
            fg.add_to(m)
            groups[cat] = (MarkerCluster().add_to(fg) if cat in CLUSTER_CATS else fg)
        up = s.get("upwind")
        popup = (f"<b>{html.escape(s['name'])}</b><br>{html.escape(cat)}<br>"
                 f"距離 {s['dist_km']:.2f} km，位於監測點 {compass(s['bearing'])}方 ({s['bearing']:.0f}°)<br>"
                 f"{'<b style=color:#d62728>⚠ 位於上風處</b><br>' if up else ''}"
                 f"來源：{s['source']} {html.escape(s.get('note', ''))}")
        folium.CircleMarker([s["lat"], s["lon"]], radius=7 if up else 4, color="#d62728" if up else colors.get(cat, "#555"),
                            fill=True, fill_color=colors.get(cat, "#555"), fill_opacity=0.8,
                            weight=3 if up else 1, popup=folium.Popup(popup, max_width=300),
                            tooltip=f"{s['name']} ({s['dist_km']:.1f} km)").add_to(groups[cat])

    fg = folium.FeatureGroup(name="🔥 FIRMS 火點/熱異常").add_to(m)
    for f in fires:
        ind = f.get("industrial")
        note = (f"<b style=color:#7f7f7f>疑似工業熱源</b>：距 {html.escape(f['near_source'])} {f['near_km']} km<br>"
                if ind else "<b style=color:#d62728>非已知工業熱源附近，需查證</b><br>")
        folium.Marker([f["lat"], f["lon"]],
                      icon=folium.Icon(color="gray" if ind else "red", icon="fire", prefix="fa"),
                      popup=folium.Popup(f"火點 {f['time']}<br>{note}信心 {f['confidence']}，FRP {f['frp']} MW<br>"
                                         f"{f['product']}", max_width=300)).add_to(fg)
    folium.LayerControl(collapsed=False).add_to(m)

    # 側欄摘要
    up_top = [s for s in sources if s.get("upwind") and s["category"] not in CLUSTER_CATS][:12]
    cnt = {}
    for s in sources:
        cnt[s["category"]] = cnt.get(s["category"], 0) + 1
    h = [f"<div style='position:fixed;top:10px;right:10px;z-index:9999;width:330px;max-height:80vh;overflow:auto;"
         "background:#fff;padding:10px;border:1px solid #888;border-radius:6px;font:12px/1.5 sans-serif'>",
         f"<b>污染源溯源 {t:%Y-%m-%d %H:%M}</b><br>{lat:.5f}, {lon:.5f}　半徑 {radius:g} km<br>"]
    if wind:
        h.append(f"風：自{compass(wind['dir'])}方 {wind['dir']:.0f}°，{wind['speed']:.1f} m/s，前3h降雨 {wind['precip']:.1f} mm<br>")
    else:
        h.append("風：氣象資料取得失敗<br>")
    h.append("<hr><b>固定源統計</b><br>" + "<br>".join(f"{html.escape(k)}：{v}" for k, v in cnt.items()))
    h.append(f"<br>🔥 火點：{len(fires)}（疑似工業熱源 {sum(1 for f in fires if f.get('industrial'))}，灰色）")
    if up_top:
        h.append("<hr><b>上風處最近的工業/能源類污染源</b><br>" + "<br>".join(
            f"{s['dist_km']:.1f} km {compass(s['bearing'])}｜{html.escape(s['name'])}" for s in up_top))
    h.append(f"<hr><b>事件線索（新聞，{'、'.join(places)}）</b><br>")
    h.append("<br>".join(f"{n['published'][5:16]} <a href='{html.escape(n['link'])}' target='_blank'>"
                         f"{html.escape(n['title'])}</a>" for n in news[:25]) or "無符合時間範圍之新聞")
    h.append("<br><i>新聞位置不精確，請自行判讀；OSM 資料不等於合法登記清單。</i></div>")
    m.get_root().html.add_child(folium.Element("".join(h)))
    m.save(out_dir / "map.html")


def write_csv(path, rows):
    if not rows:
        return
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)


def main():
    ap = argparse.ArgumentParser(description="污染源溯源資料收集")
    ap.add_argument("--lat", type=float, required=True)
    ap.add_argument("--lon", type=float, required=True)
    ap.add_argument("--time", required=True, help='例 "2026-11-22 14:00"（預設台北時間）')
    ap.add_argument("--radius", type=float, default=10.0, help="公里")
    ap.add_argument("--window-hours", type=float, default=24.0, help="往前回溯小時數")
    ap.add_argument("--extra-sources", default="data/stationary_sources.csv")
    ap.add_argument("--out", default="output")
    ap.add_argument("--industrial-buffer", type=float, default=0.8,
                    help="火點距工業熱源多少公里內視為疑似工業熱源")
    a = ap.parse_args()
    if not in_taiwan(a.lat, a.lon):
        sys.exit(f"座標 ({a.lat}, {a.lon}) 不在台灣範圍內（本程式僅限台灣）")

    t = datetime.fromisoformat(a.time.replace("T", " "))
    t = t.replace(tzinfo=TZ) if t.tzinfo is None else t.astimezone(TZ)
    t0 = t - timedelta(hours=a.window_hours)
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)

    def safe(label, fn, default):
        print(f"→ {label}")
        try:
            return fn()
        except Exception as e:
            print(f"  ✗ {label} 失敗: {e}", file=sys.stderr)
            return default

    wind = safe("氣象", lambda: collect_wind(a.lat, a.lon, t), None)
    sources = safe("OSM 固定源/施工/廟宇", lambda: collect_osm(a.lat, a.lon, a.radius), [])
    sources += collect_extra(a.extra_sources)
    sources = [s for s in sources]
    for s in sources:
        s["dist_km"] = round(haversine(a.lat, a.lon, s["lat"], s["lon"]), 3)
        s["bearing"] = round(bearing(a.lat, a.lon, s["lat"], s["lon"]), 1)
        s["upwind"] = bool(wind) and angdiff(s["bearing"], wind["dir"]) <= 45
    sources = sorted([s for s in sources if s["dist_km"] <= a.radius], key=lambda s: s["dist_km"])
    fires = safe("FIRMS 火點", lambda: collect_fires(a.lat, a.lon, a.radius, t0, t, os.getenv("FIRMS_MAP_KEY")), [])
    flag_industrial_fires(fires, sources, a.industrial_buffer)
    places = safe("反向地理編碼", lambda: reverse_geocode(a.lat, a.lon), [])
    news = safe("新聞事件線索", lambda: collect_news(places, t0, t), []) if places else []

    write_csv(out / "sources.csv", sources)
    write_csv(out / "fires.csv", fires)
    write_csv(out / "news.csv", news)
    summary = dict(lat=a.lat, lon=a.lon, time=t.isoformat(), radius_km=a.radius, wind=wind, places=places,
                   n_sources=len(sources), n_upwind=sum(s["upwind"] for s in sources),
                   n_fires=len(fires), n_fires_industrial=sum(f.get("industrial", False) for f in fires),
                   n_news=len(news))
    (out / "summary.json").write_text(json.dumps(summary, ensure_ascii=False, indent=2), encoding="utf-8")
    build_map(a.lat, a.lon, a.radius, t, wind, sources, fires, news, places, out)

    with open(out / "summary.md", "w", encoding="utf-8") as f:
        f.write(f"## 污染源溯源 {t:%Y-%m-%d %H:%M}\n\n- 位置：{a.lat}, {a.lon}（半徑 {a.radius:g} km）\n"
                f"- 固定源/設施：{len(sources)}（上風處 {summary['n_upwind']}）\n- FIRMS 火點：{len(fires)}（疑似工業熱源 {summary['n_fires_industrial']}）\n"
                f"- 新聞線索：{len(news)}\n- 風：{'自%s方 %.0f°，%.1f m/s' % (compass(wind['dir']), wind['dir'], wind['speed']) if wind else '無資料'}\n"
                "\n下載 Artifact 內的 `map.html` 以瀏覽互動地圖。\n")
    print(json.dumps(summary, ensure_ascii=False))


if __name__ == "__main__":
    main()
