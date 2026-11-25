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
    "https://overpass.private.coffee/api/interpreter",
    "https://overpass.kumi.systems/api/interpreter",
]
# 底圖：OSM 官方圖磚要求 Referer，本機/手機直接開 map.html 會被 403 擋，故不用
BASEMAPS = [
    ("臺灣通用電子地圖(NLSC)", "https://wmts.nlsc.gov.tw/wmts/EMAP/default/GoogleMapsCompatible/{z}/{y}/{x}",
     "&copy; 內政部國土測繪中心"),
    ("CartoDB 淺色", "https://{s}.basemaps.cartocdn.com/rastertiles/voyager/{z}/{x}/{y}{r}.png",
     "&copy; OpenStreetMap contributors &copy; CARTO"),
    ("Esri 衛星影像", "https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}",
     "Tiles &copy; Esri"),
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
    # 拆成兩類分開查：道路施工線段資料量大、最常逾時，失敗時不會連帶工地一起沒資料
    "工地(建案/營建)": (['nwr["landuse"="construction"]'], "#2ca02c"),
    "道路施工": (['way["highway"="construction"]'], "#98df8a"),
}
CLUSTER_CATS = {"加油站(VOC)", "廟宇(香燭/金爐/鞭炮/繞境)"}
FIRMS_SATS = ["VIIRS_SNPP", "VIIRS_NOAA20", "VIIRS_NOAA21"]
HEAT_CATS = {"工業區/工廠", "煙囪/儲槽/燃燒塔", "電廠/發電設施", "自備固定源"}  # 會持續發熱、易被誤判成火點
# 台灣範圍（概略框：本島+離島、澎湖、馬祖、金門）(lat_min, lat_max, lon_min, lon_max)
TAIWAN_BOXES = [(21.8, 25.4, 120.0, 122.1), (23.1, 23.85, 119.3, 119.75),
                (25.9, 26.4, 119.9, 120.6), (24.3, 24.6, 118.15, 118.6)]
NEWS_KEYWORDS = ["火災", "繞境", "廟會", "煙火", "焚燒", "道路施工", "空污", "工廠 異味"]
# 標題含這些字 → 多半是廣告/宣導/評論，列為「疑似無關」（不刪除，只降級顯示）
NEWS_NOISE = ["飯店", "酒店", "優惠", "懶人包", "開箱", "房", "派對", "門票", "行動電源", "鋰電池",
              "宣導", "呼籲", "示警", "須知", "防範", "身障", "當年", "回顧",
              "車掃", "造勢", "政見", "選戰", "參選", "市長", "議員", "虐童", "AI"]
# 標題關鍵字（Google News 會比對內文，標題沒提到就多半無關）
NEWS_TITLE_HINTS = {"火災": ["火", "燒", "濃煙", "黑煙"], "繞境": ["繞境", "遶境", "進香"],
                    "廟會": ["廟", "宮", "王船", "醮"], "煙火": ["煙火", "鞭炮", "炮"],
                    "焚燒": ["焚", "燒", "王船"], "道路施工": ["施工", "挖掘", "封路", "管制"],
                    "空污": ["空污", "空品", "PM2.5", "異味", "臭", "煙霧", "霾"],
                    "工廠 異味": ["異味", "臭", "工廠"]}
TW_CITIES = ["臺北", "台北", "新北", "基隆", "桃園", "新竹", "苗栗", "臺中", "台中", "彰化", "南投", "雲林",
             "嘉義", "臺南", "台南", "高雄", "屏東", "宜蘭", "花蓮", "臺東", "台東", "澎湖", "金門", "連江", "馬祖"]
FAILED = []  # 各蒐集步驟失敗紀錄，寫入地圖與 summary，避免「0 筆」與「查詢失敗」混淆


def http(method, url, retries=3, backoff=5, **kw):
    """含重試的 HTTP；429/5xx 會等待後重試（GitHub Actions 共用 IP 常被限流）。"""
    kw.setdefault("headers", UA)
    last = None
    for i in range(retries):
        try:
            r = requests.request(method, url, **kw)
            if r.status_code in (429, 500, 502, 503, 504):
                raise requests.HTTPError(f"HTTP {r.status_code}", response=r)
            r.raise_for_status()
            return r
        except Exception as e:
            last = e
            if i < retries - 1:
                time.sleep(backoff * (i + 1))
    raise last


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
OSM_CACHE_DIR = Path(os.getenv("OSM_CACHE_DIR", "cache/osm"))
OSM_CACHE_DAYS = 30  # 固定設施變動慢，30 天內直接用快取，減少 Overpass 負載
OSM_BUDGET_S = float(os.getenv("OSM_BUDGET_S", 480))  # OSM 查詢總時間上限，超過即跳過，避免整個 job 逾時


def _osm_query(cat, filters, bbox, deadline):
    """以 bbox 查詢（比 around 快很多），距離在 Python 端再篩。回傳 elements 或丟例外。"""
    parts = "".join(f"{f}({bbox});" for f in filters)
    query = f"[out:json][timeout:60];({parts});out center tags;"
    errs = []
    for url in OVERPASS:
        left = deadline - time.monotonic()
        if left < 20:
            errs.append("超過查詢時間上限")
            break
        try:
            r = http("POST", url, retries=1, data={"data": query}, timeout=min(75, left))
            data = r.json()
            if "runtime error" in data.get("remark", ""):  # 逾時但回 200
                raise RuntimeError(data["remark"][:100])
            return data.get("elements", [])
        except Exception as e:  # 換下一個鏡像
            errs.append(f"{url.split('/')[2]}: {str(e)[:80]}")
            print(f"  [overpass] {cat} @ {url}: {e}", file=sys.stderr)
    raise RuntimeError("；".join(errs))


OSM_SNAPSHOT = Path(os.getenv("OSM_SNAPSHOT", "data/osm_taiwan.csv.gz"))


def collect_osm_snapshot(lat, lon, radius_km):
    """讀本地全臺 OSM 快照（每月由 update_osm.yml 產生），不需連 Overpass。"""
    import gzip
    meta = OSM_SNAPSHOT.with_name("osm_taiwan.meta.json")
    built = json.loads(meta.read_text(encoding="utf-8")).get("built", "")[:10] if meta.exists() else "?"
    out = []
    with gzip.open(OSM_SNAPSHOT, "rt", encoding="utf-8") as f:
        for r in csv.DictReader(f):
            la, lo = float(r["lat"]), float(r["lon"])
            if abs(la - lat) > radius_km / 100 or haversine(lat, lon, la, lo) > radius_km:
                continue
            out.append(dict(name=r["name"], category=r["category"], lat=la, lon=lo,
                            source=f"OSM快照({built})", note=r["note"]))
    print(f"  [osm] 使用本地快照 {OSM_SNAPSHOT}（{built}），範圍內 {len(out)} 筆", file=sys.stderr)
    return out


def collect_osm(lat, lon, radius_km):
    if OSM_SNAPSHOT.exists():
        try:
            return collect_osm_snapshot(lat, lon, radius_km)
        except Exception as e:
            print(f"  [osm] 快照讀取失敗，改查 Overpass：{e}", file=sys.stderr)
    # 快取以 0.01° 網格 + 半徑為鍵；同一地點重跑不必再查 Overpass
    key = f"{lat:.2f}_{lon:.2f}_{radius_km:g}"
    dlat = radius_km / 111.0
    dlon = radius_km / (111.0 * math.cos(math.radians(lat)))
    bbox = f"{lat - dlat:.5f},{lon - dlon:.5f},{lat + dlat:.5f},{lon + dlon:.5f}"
    out = []
    deadline = time.monotonic() + OSM_BUDGET_S
    for cat, (filters, _) in OSM_CATEGORIES.items():
        cf = OSM_CACHE_DIR / key / f"{cat.replace('/', '_')}.json"
        cached, age = None, None
        if cf.exists():
            c = json.loads(cf.read_text(encoding="utf-8"))
            cached = c["elements"]
            age = (datetime.now(TZ) - datetime.fromisoformat(c["fetched"])).days
        if cached is not None and age <= OSM_CACHE_DAYS:
            elements = cached
            print(f"  [osm] {cat}: 使用快取（{age} 天前）", file=sys.stderr)
        else:
            try:
                elements = _osm_query(cat, filters, bbox, deadline)
                cf.parent.mkdir(parents=True, exist_ok=True)
                cf.write_text(json.dumps(dict(fetched=datetime.now(TZ).isoformat(), elements=elements),
                                         ensure_ascii=False), encoding="utf-8")
                time.sleep(3)  # 對 Overpass 客氣一點
            except Exception as e:
                if cached is not None:
                    elements = cached
                    FAILED.append(f"OSM {cat}：Overpass 查詢失敗，改用 {age} 天前快取")
                else:
                    FAILED.append(f"OSM {cat}：所有 Overpass 鏡像查詢失敗（未取得，非 0 筆）")
                    continue
        for el in elements:
            tags = el.get("tags", {})
            la = el.get("lat") or el.get("center", {}).get("lat")
            lo = el.get("lon") or el.get("center", {}).get("lon")
            if la is None or lo is None:
                continue
            name = tags.get("name:zh") or tags.get("name") or tags.get("operator") or "(未命名)"
            out.append(dict(name=name, category=cat, lat=la, lon=lo, source="OSM",
                            note=f"osm:{el['type']}/{el['id']}"))
    return out


def collect_extra(path):
    if not path or not Path(path).exists():
        return []
    out = []
    with open(path, encoding="utf-8-sig") as f:
        for row in csv.DictReader(f):
            if (row.get("name") or "").startswith("範例"):  # 範本列不納入
                continue
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
    archive, forecast = "https://archive-api.open-meteo.com/v1/archive", "https://api.open-meteo.com/v1/forecast"
    # archive 約有 5 天延遲；近期用 forecast（含過去資料），兩者互為備援
    urls = [archive, forecast] if age > 5 else [forecast, archive]
    params = dict(latitude=lat, longitude=lon, timezone="Asia/Taipei", wind_speed_unit="ms",
                  start_date=(t - timedelta(days=1)).date().isoformat(), end_date=t.date().isoformat(),
                  hourly="wind_speed_10m,wind_direction_10m,temperature_2m,precipitation")
    errs = []
    h = None
    for url in urls:
        try:
            h = http("GET", url, params=params, timeout=30).json()["hourly"]
            break
        except Exception as e:
            errs.append(f"{url.split('/')[2]}: {e}")
    if h is None:
        raise RuntimeError("；".join(errs))
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


# ---------------------------------------------------------------- 測站風向
def _pick(rec, *names):
    """欄位名稱不分大小寫取值（環境部 API 欄位大小寫不一）。"""
    low = {k.lower(): v for k, v in rec.items()}
    for n in names:
        v = low.get(n.lower())
        if v not in (None, "", "-", "--", "x", "X"):
            return v
    return None


def _num(v):
    try:
        x = float(v)
        return None if x < 0 or x > 990 else x  # -99/999 等缺值
    except (TypeError, ValueError):
        return None


def _parse_ts(v):
    if not v:
        return None
    v = str(v).replace("/", "-").replace("T", " ")[:19]
    for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M"):
        try:
            return datetime.strptime(v, fmt).replace(tzinfo=TZ)
        except ValueError:
            continue
    try:
        d = datetime.fromisoformat(v)
        return d.replace(tzinfo=TZ) if d.tzinfo is None else d.astimezone(TZ)
    except ValueError:
        return None


def collect_moenv_wind(lat, lon, t, search_km, key):
    """環境部空品測站逐時風向風速（AQX_P_488 空氣品質指標歷史資料）。"""
    if not key:
        FAILED.append("環境部測站風向：未設定 MOENV_API_KEY，未查詢")
        return []
    t0, t1 = t - timedelta(hours=3), t + timedelta(hours=1)
    base = "https://data.moenv.gov.tw/api/v2/aqx_p_488"
    records = None
    # 依序嘗試：伺服器端日期篩選（欄位名大小寫兩種）→ 不篩選取最新大量資料
    for flt in (f"datacreationdate,GR,{t0:%Y-%m-%d %H:%M:%S}|datacreationdate,LE,{t1:%Y-%m-%d %H:%M:%S}",
                f"DataCreationDate,GR,{t0:%Y-%m-%d %H:%M:%S}|DataCreationDate,LE,{t1:%Y-%m-%d %H:%M:%S}",
                None):
        params = dict(api_key=key, format="JSON", limit=1000)
        if flt:
            params["filters"] = flt
        try:
            js = http("GET", base, params=params, timeout=60).json()
        except Exception as e:
            print(f"  [moenv] 查詢失敗 filters={flt}: {e}", file=sys.stderr)
            continue
        recs = js.get("records", js) if isinstance(js, dict) else js
        if isinstance(recs, list) and recs:
            print(f"  [moenv] filters={flt} → {len(recs)} 筆；欄位：{list(recs[0].keys())}", file=sys.stderr)
            inwin = [r for r in recs if (d := _parse_ts(_pick(r, "datacreationdate", "publishtime")))
                     and t0 <= d <= t1]
            if inwin:
                records = inwin
                break
            print(f"  [moenv] 回傳資料不在 {t0:%m-%d %H:%M}~{t1:%m-%d %H:%M} 內，換下一種查詢", file=sys.stderr)
        else:
            print(f"  [moenv] filters={flt} → 無資料：{str(js)[:200]}", file=sys.stderr)
    if not records:
        FAILED.append("環境部測站風向：查無事件時段資料（詳見 Actions log 的 [moenv]）")
        return []
    out = []
    for r in records:
        la, lo = _num(_pick(r, "latitude")), _num(_pick(r, "longitude"))
        wd, ws = _num(_pick(r, "winddirec", "wind_direc")), _num(_pick(r, "windspeed", "wind_speed"))
        if la is None or lo is None or wd is None or ws is None:
            continue
        dist = haversine(lat, lon, la, lo)
        if dist <= search_km:
            out.append(dict(source="環境部", station=_pick(r, "sitename") or "?", lat=la, lon=lo,
                            time=_parse_ts(_pick(r, "datacreationdate", "publishtime")).isoformat(timespec="minutes"),
                            dir=wd % 360, speed=ws, dist_km=round(dist, 2)))
    return out


def collect_cwa_wind(lat, lon, t, search_km, key):
    """氣象署自動氣象站（O-A0001-001）——API 只提供最新觀測，事件在 90 分鐘內才有用。"""
    if not key:
        FAILED.append("氣象署測站風向：未設定 CWA_API_KEY，未查詢")
        return []
    if abs((datetime.now(TZ) - t).total_seconds()) > 5400:
        print("  [cwa] 事件時間距今超過 90 分鐘，氣象署 API 僅提供最新觀測，略過", file=sys.stderr)
        return []
    js = http("GET", "https://opendata.cwa.gov.tw/api/v1/rest/datastore/O-A0001-001",
              params=dict(Authorization=key, format="JSON"), timeout=60).json()
    out = []
    for st in js.get("records", {}).get("Station", []):
        coords = st.get("GeoInfo", {}).get("Coordinates", [])
        c = next((c for c in coords if "WGS84" in str(c.get("CoordinateName", ""))), coords[0] if coords else {})
        la, lo = _num(c.get("StationLatitude")), _num(c.get("StationLongitude"))
        we = st.get("WeatherElement", {})
        wd, ws = _num(we.get("WindDirection")), _num(we.get("WindSpeed"))
        if None in (la, lo, wd, ws):
            continue
        dist = haversine(lat, lon, la, lo)
        if dist <= search_km:
            out.append(dict(source="氣象署", station=st.get("StationName", "?"), lat=la, lon=lo,
                            time=str(st.get("ObsTime", {}).get("DateTime", ""))[:16],
                            dir=wd % 360, speed=ws, dist_km=round(dist, 2)))
    print(f"  [cwa] 範圍內 {len(out)} 站", file=sys.stderr)
    return out


def station_wind(obs):
    """各測站先做時間向量平均，再以 1/d² 加權得到代表風向。"""
    by = {}
    for o in obs:
        by.setdefault((o["source"], o["station"]), []).append(o)
    stations, X, Y, W = [], 0.0, 0.0, 0.0
    for (src, name), rows in by.items():
        x = sum(r["speed"] * math.sin(math.radians(r["dir"])) for r in rows) / len(rows)
        y = sum(r["speed"] * math.cos(math.radians(r["dir"])) for r in rows) / len(rows)
        spd = sum(r["speed"] for r in rows) / len(rows)
        d = (math.degrees(math.atan2(x, y)) + 360) % 360
        # 風向穩定度：向量平均風速/純量平均風速（1=風向一致，接近0=風向亂或靜風）
        steady = math.hypot(x, y) / spd if spd > 0 else 0
        r0 = rows[0]
        stations.append(dict(source=src, station=name, lat=r0["lat"], lon=r0["lon"], dist_km=r0["dist_km"],
                             dir=d, speed=spd, steady=steady, n=len(rows),
                             hourly=sorted(((r["time"][11:16], r["dir"], r["speed"]) for r in rows))))
        w = 1 / max(r0["dist_km"], 0.5) ** 2
        X, Y, W = X + w * x, Y + w * y, W + w
    stations.sort(key=lambda s: s["dist_km"])
    if not stations:
        return None, []
    d = (math.degrees(math.atan2(X / W, Y / W)) + 360) % 360
    return dict(dir=d, speed=sum(s["speed"] for s in stations) / len(stations), precip=0.0,
                hours=max(s["n"] for s in stations), source=f"測站（{len(stations)} 站距離加權）"), stations


def in_taiwan(lat, lon):
    return any(a <= lat <= b and c <= lon <= d for a, b, c, d in TAIWAN_BOXES)


def collect_fires(lat, lon, radius_km, t0, t1, key):
    """同時查 SNPP / NOAA-20 / NOAA-21 三顆 VIIRS，增加過境次數。"""
    if not key:
        print("  [firms] 未設定 FIRMS_MAP_KEY，略過火點", file=sys.stderr)
        FAILED.append("FIRMS 火點：未設定 FIRMS_MAP_KEY，未查詢（不是 0 筆）")
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
            FAILED.append(f"FIRMS {src}：{str(e)[:100]}")
            continue
        for row in csv.DictReader(r.text.splitlines()):
            la, lo = float(row["latitude"]), float(row["longitude"])
            acq = datetime.strptime(row["acq_date"] + row["acq_time"].zfill(4), "%Y-%m-%d%H%M").replace(
                tzinfo=timezone.utc)
            if u0 <= acq <= u1 and haversine(lat, lon, la, lo) <= radius_km:
                out.append(dict(lat=la, lon=lo, time=acq.astimezone(TZ).isoformat(timespec="minutes"),
                                confidence=row.get("confidence", ""), frp=row.get("frp", ""), product=src))
    print(f"  [firms] 查詢成功，窗內火點 {len(out)} 筆", file=sys.stderr)
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


def _geocode1(lat, lon):
    r = http("GET", "https://nominatim.openstreetmap.org/reverse", timeout=30,
             params=dict(lat=lat, lon=lon, format="jsonv2", zoom=14, **{"accept-language": "zh-TW"}))
    ad = r.json().get("address", {})
    district = next((ad[k] for k in ("suburb", "city_district", "town", "village") if k in ad), None)
    city = ad.get("city") or ad.get("county") or ad.get("state")
    return district, city


def reverse_geocode(lat, lon, radius_km=0, wind=None):
    """監測點所在區 + 半徑內鄰近行政區（上風方向優先）。回傳 [區..., 市...]。"""
    district, city = _geocode1(lat, lon)
    districts, cities = [district], [city]
    if radius_km > 0:
        brgs = list(range(0, 360, 45))
        if wind:  # 上風扇區多取點
            brgs = [wind["dir"] - 30, wind["dir"], wind["dir"] + 30] + brgs
        for b in brgs:
            for k in (0.4, 0.8):
                time.sleep(1.1)  # Nominatim 限 1 req/s
                try:
                    d, c = _geocode1(*destination(lat, lon, b % 360, radius_km * k))
                except Exception:
                    continue
                districts.append(d)
                cities.append(c)
    names = [n for n in dict.fromkeys(districts) if n][:8]
    return names + [n for n in dict.fromkeys(cities) if n and n not in names]


def collect_news(places, t0, t1):
    local = {c for c in TW_CITIES for p in places if c[:2] in p.replace("台", "臺") or c in p}
    local |= {c.replace("臺", "台") for c in local} | {c.replace("台", "臺") for c in local}
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
                    link, title = it.findtext("link"), it.findtext("title") or ""
                    head = title.rsplit(" - ", 1)[0]  # 去掉「- 媒體名」
                    noise = [w for w in NEWS_NOISE if w in head]
                    if not any(h in head for h in NEWS_TITLE_HINTS.get(kw, [kw])):
                        noise.append(f"標題無「{kw}」相關字")
                    far = [c for c in TW_CITIES if c in head and c not in local]
                    if far:
                        noise.append(f"外縣市:{far[0]}")
                    if dt > t1:
                        timing = "事件時間後發布"
                    elif dt < t0:
                        timing = "回溯窗前發布"
                    else:
                        timing = "回溯窗內"
                    items.setdefault(link, dict(title=title, link=link,
                                                published=dt.isoformat(timespec="minutes"),
                                                media=it.findtext("source") or "", keyword=kw, place=name,
                                                timing=timing, relevant=not noise,
                                                noise_words="/".join(noise)))
            time.sleep(1)
    # 相關者在前；同組依時間新→舊
    news = sorted(items.values(), key=lambda x: x["published"], reverse=True)
    return sorted(news, key=lambda x: not x["relevant"])  # stable：相關者在前，各組內新→舊


# ---------------------------------------------------------------- 衛星影像
# NASA GIBS 每日真實色彩影像（解析度約 250–375 m，看得到大範圍濃煙/煙羽，看不到小火）
GIBS_LAYERS = [("VIIRS SNPP", "VIIRS_SNPP_CorrectedReflectance_TrueColor"),
               ("VIIRS NOAA-20", "VIIRS_NOAA20_CorrectedReflectance_TrueColor"),
               ("MODIS Aqua", "MODIS_Aqua_CorrectedReflectance_TrueColor")]
GIBS_URL = ("https://gibs.earthdata.nasa.gov/wmts/epsg3857/best/{layer}/default/{date}/"
            "GoogleMapsCompatible_Level9/{{z}}/{{y}}/{{x}}.jpg")


def worldview_url(lat, lon, day, km=15):
    """NASA Worldview：指定日期的衛星真實色彩 + VIIRS 火點圖層。"""
    d = km / 111.0
    return ("https://worldview.earthdata.nasa.gov/?v="
            f"{lon - d * 1.5:.3f},{lat - d:.3f},{lon + d * 1.5:.3f},{lat + d:.3f}&t={day}-T05:30:00Z"
            "&l=Coastlines_15m,VIIRS_NOAA20_Thermal_Anomalies_375m_All,VIIRS_SNPP_Thermal_Anomalies_375m_All,"
            "VIIRS_SNPP_CorrectedReflectance_TrueColor")


def copernicus_url(lat, lon, t, days=7):
    """Copernicus Browser：Sentinel-2（10 m，約 5 天一次，常被雲遮）事件前 N 天的影像。"""
    t0 = (t - timedelta(days=days)).astimezone(timezone.utc)
    t1 = (t + timedelta(days=1)).astimezone(timezone.utc)
    return (f"https://browser.dataspace.copernicus.eu/?zoom=14&lat={lat:.5f}&lng={lon:.5f}"
            f"&fromTime={t0:%Y-%m-%dT00:00:00.000Z}&toTime={t1:%Y-%m-%dT23:59:59.999Z}&datasetId=S2_L2A_CDAS")


def sat_links(lat, lon, t):
    days = [(t - timedelta(days=1)).date().isoformat(), t.date().isoformat()]
    wv = "／".join(f"<a href='{html.escape(worldview_url(lat, lon, d))}' target='_blank'>{d[5:]}</a>" for d in days)
    return (f"🛰️ NASA Worldview（每日影像＋火點）：{wv}　"
            f"<a href='{html.escape(copernicus_url(lat, lon, t))}' target='_blank'>Sentinel-2 高解析</a>")


# ---------------------------------------------------------------- 地圖
def build_map(lat, lon, radius, t, wind, sources, fires, news, places, out_dir, stations=(), model_wind=None):
    m = folium.Map(location=[lat, lon], zoom_start=12, tiles=None)
    for i, (name, url, attr) in enumerate(BASEMAPS):
        folium.TileLayer(url, name=name, attr=attr, max_zoom=19, show=(i == 0), overlay=False,
                         control=True).add_to(m)
    # 事件當天與前一天的衛星每日影像（疊加圖層，預設關閉；VIIRS 約臺灣時間 13:30 過境）
    for d in [(t - timedelta(days=1)).date().isoformat(), t.date().isoformat()]:
        for label, layer in GIBS_LAYERS[:2]:
            folium.TileLayer(GIBS_URL.format(layer=layer, date=d), name=f"🛰️ {d[5:]} {label} 衛星影像",
                             attr="NASA GIBS", max_native_zoom=9, max_zoom=19, overlay=True, show=False,
                             opacity=0.85).add_to(m)
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

    if stations:
        sg = folium.FeatureGroup(name="🧭 測站風向（線指向風吹去的方向）").add_to(m)
        for st in stations:
            tip = destination(st["lat"], st["lon"], (st["dir"] + 180) % 360, 0.4 + 0.25 * min(st["speed"], 8))
            col = "#1f77b4" if st["source"] == "環境部" else "#2ca02c"
            folium.PolyLine([[st["lat"], st["lon"]], list(tip)], color=col, weight=4).add_to(sg)
            rows = "".join(f"<tr><td>{h}</td><td>{compass(d)} {d:.0f}°</td><td>{v:.1f}</td></tr>"
                           for h, d, v in st["hourly"])
            folium.CircleMarker([st["lat"], st["lon"]], radius=6, color=col, fill=True, fill_opacity=1,
                                tooltip=f"{st['source']} {st['station']}：自{compass(st['dir'])} {st['speed']:.1f} m/s",
                                popup=folium.Popup(
                                    f"<b>{st['source']} {html.escape(st['station'])}</b>（距 {st['dist_km']} km）<br>"
                                    f"平均：自{compass(st['dir'])}方 {st['dir']:.0f}°，{st['speed']:.1f} m/s，"
                                    f"穩定度 {st['steady']:.2f}<table border=1 style=border-collapse:collapse>"
                                    f"<tr><th>時</th><th>風向</th><th>m/s</th></tr>{rows}</table>",
                                    max_width=260)).add_to(sg)

    groups = {}
    colors = {c: v[1] for c, v in OSM_CATEGORIES.items()}
    for s in sorted(sources, key=lambda x: x["dist_km"]):
        cat = s["category"]
        if cat not in groups:
            fg = folium.FeatureGroup(name=f"{cat}")
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
                                         f"{f['product']}<br>{sat_links(f['lat'], f['lon'], datetime.fromisoformat(f['time']))}",
                                         max_width=320)).add_to(fg)
    folium.LayerControl(collapsed=True).add_to(m)

    # 側欄摘要
    up_top = [s for s in sources if s.get("upwind") and s["category"] not in CLUSTER_CATS][:12]
    cnt = {}
    for s in sources:
        cnt[s["category"]] = cnt.get(s["category"], 0) + 1
    # 可收合側欄（手機上預設收合，不擋地圖）
    h = ["<details id='pt-panel' style='position:fixed;bottom:10px;left:10px;z-index:9999;"
         "width:min(340px,85vw);max-height:70vh;overflow:auto;background:#fff;padding:8px 10px;"
         "border:1px solid #888;border-radius:6px;font:12px/1.5 sans-serif'>",
         f"<summary style='cursor:pointer'><b>污染源溯源 {t:%Y-%m-%d %H:%M}</b>（點此展開/收合）</summary>",
         "<script>if(window.innerWidth>800)document.getElementById('pt-panel').open=true;</script>",
         f"{lat:.5f}, {lon:.5f}　半徑 {radius:g} km<br>"]
    if wind:
        src = "手動輸入" if wind.get("manual") else wind.get("source", "Open-Meteo 模式網格值")
        h.append(f"<b>判定用風向</b>：自{compass(wind['dir'])}方 {wind['dir']:.0f}°，{wind['speed']:.1f} m/s（{src}）<br>")
        if model_wind and model_wind is not wind:
            diff = angdiff(model_wind["dir"], wind["dir"])
            h.append(f"模式風（Open-Meteo）：自{compass(model_wind['dir'])}方 {model_wind['dir']:.0f}°，"
                     f"{model_wind['speed']:.1f} m/s，與判定風向差 {diff:.0f}°"
                     f"{'（差異大，上風判斷請保守看待）' if diff > 45 else ''}<br>")
        if stations:
            h.append("<details><summary>測站風向（事件前3h～後1h平均）</summary>" + "<br>".join(
                f"{s['source']} {html.escape(s['station'])} {s['dist_km']} km：自{compass(s['dir'])} {s['dir']:.0f}° "
                f"{s['speed']:.1f} m/s{'，風向不穩' if s['steady'] < 0.6 else ''}" for s in stations) + "</details>")
    else:
        h.append("<b style=color:#d62728>風：氣象資料取得失敗 → 無法判斷上風處</b>"
                 "（可用 --wind-dir/--wind-speed 手動輸入測站風向）<br>")
    if FAILED:
        h.append("<hr><b style=color:#d62728>⚠ 資料查詢失敗（以下類別為「未取得」，不是 0 筆）</b><br>"
                 + "<br>".join(html.escape(x) for x in FAILED))
    h.append("<hr><b>固定源統計</b><br>" + "<br>".join(f"{html.escape(k)}：{v}" for k, v in cnt.items()))
    h.append(f"<br>🔥 火點：{len(fires)}（疑似工業熱源 {sum(1 for f in fires if f.get('industrial'))}，灰色）")
    h.append(f"<br>{sat_links(lat, lon, t)}<br><span style=color:#888>右上圖層可疊加當天/前一天衛星影像"
             "（解析度約 300 m，看煙羽用）</span>")
    if up_top:
        h.append("<hr><b>上風處最近的工業/能源類污染源</b><br>" + "<br>".join(
            f"{s['dist_km']:.1f} km {compass(s['bearing'])}｜{html.escape(s['name'])}" for s in up_top))
    def fmt(n):
        tag = "" if n["timing"] == "回溯窗內" else f" <span style=color:#999>[{n['timing']}]</span>"
        return (f"{n['published'][5:16]} <a href='{html.escape(n['link'])}' target='_blank'>"
                f"{html.escape(n['title'])}</a>{tag}")
    rel = [n for n in news if n["relevant"]]
    noise = [n for n in news if not n["relevant"]]
    h.append(f"<hr><b>事件線索（新聞，{'、'.join(places)}）</b><br>")
    h.append("<br>".join(fmt(n) for n in rel[:25]) or "無符合時間範圍之新聞")
    if noise:
        h.append(f"<details><summary style=color:#999>疑似無關（廣告/宣導等）{len(noise)} 則</summary>"
                 + "<br>".join(fmt(n) for n in noise[:25]) + "</details>")
    h.append("<br><i>新聞位置不精確，請自行判讀；OSM 資料不等於合法登記清單；"
             "OSM 施工路段常有過期標註。</i></details>")
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
    ap.add_argument("--wind-dir", type=float, help="手動風向（度，風吹來的方向；如測站資料），優先於 Open-Meteo")
    ap.add_argument("--wind-speed", type=float, default=0.0, help="手動風速 m/s")
    ap.add_argument("--industrial-buffer", type=float, default=0.8,
                    help="火點距工業熱源多少公里內視為疑似工業熱源")
    a = ap.parse_args()
    if not in_taiwan(a.lat, a.lon):
        sys.exit(f"座標 ({a.lat}, {a.lon}) 不在台灣範圍內（本程式僅限台灣）")

    # 容錯：前後空白、全形空白、斜線日期、T 分隔（例 " 2026/11/22 14:00"）
    ts = " ".join(a.time.replace("\u3000", " ").replace("/", "-").replace("T", " ").split())
    try:
        t = datetime.fromisoformat(ts)
    except ValueError:
        sys.exit(f"時間格式無法辨識：{a.time!r}，請用「2026-11-22 14:00」格式")
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
            FAILED.append(f"{label}：{str(e)[:150]}")
            return default

    search_km = max(15.0, a.radius)
    obs = safe("環境部測站風向", lambda: collect_moenv_wind(a.lat, a.lon, t, search_km, os.getenv("MOENV_API_KEY", "").strip()), [])
    obs += safe("氣象署測站風向", lambda: collect_cwa_wind(a.lat, a.lon, t, search_km, os.getenv("CWA_API_KEY", "").strip()), [])
    st_wind, stations = station_wind(obs)
    model_wind = safe("模式風（Open-Meteo）", lambda: collect_wind(a.lat, a.lon, t), None)
    if model_wind:
        model_wind["source"] = "Open-Meteo 模式網格值"
    if a.wind_dir is not None:
        wind = dict(dir=a.wind_dir % 360, speed=a.wind_speed, precip=0.0, hours=0, manual=True)
    else:
        wind = st_wind or model_wind  # 優先用測站，沒有才用模式
    sources = safe("OSM 固定源/施工/廟宇", lambda: collect_osm(a.lat, a.lon, a.radius), [])
    sources += collect_extra(a.extra_sources)
    for s in sources:
        s["dist_km"] = round(haversine(a.lat, a.lon, s["lat"], s["lon"]), 3)
        s["bearing"] = round(bearing(a.lat, a.lon, s["lat"], s["lon"]), 1)
        s["upwind"] = bool(wind) and angdiff(s["bearing"], wind["dir"]) <= 45
    sources = sorted([s for s in sources if s["dist_km"] <= a.radius], key=lambda s: s["dist_km"])
    fires = safe("FIRMS 火點", lambda: collect_fires(a.lat, a.lon, a.radius, t0, t, (os.getenv("FIRMS_MAP_KEY") or "").strip()), [])
    flag_industrial_fires(fires, sources, a.industrial_buffer)
    places = safe("反向地理編碼", lambda: reverse_geocode(a.lat, a.lon, a.radius, wind), [])
    news = safe("新聞事件線索", lambda: collect_news(places, t0, t), []) if places else []

    write_csv(out / "sources.csv", sources)
    write_csv(out / "fires.csv", fires)
    write_csv(out / "news.csv", news)
    write_csv(out / "wind_obs.csv", obs)
    summary = dict(lat=a.lat, lon=a.lon, time=t.isoformat(), radius_km=a.radius, wind=wind, places=places,
                   n_sources=len(sources), n_upwind=sum(s["upwind"] for s in sources),
                   n_fires=len(fires), n_fires_industrial=sum(f.get("industrial", False) for f in fires),
                   n_news=len(news), n_news_relevant=sum(n["relevant"] for n in news), failed=FAILED,
                   model_wind=model_wind,
                   stations=[{k: v for k, v in s.items() if k != "hourly"} for s in stations])
    (out / "summary.json").write_text(json.dumps(summary, ensure_ascii=False, indent=2), encoding="utf-8")
    build_map(a.lat, a.lon, a.radius, t, wind, sources, fires, news, places, out, stations, model_wind)

    with open(out / "summary.md", "w", encoding="utf-8") as f:
        f.write(f"## 污染源溯源 {t:%Y-%m-%d %H:%M}\n\n- 位置：{a.lat}, {a.lon}（半徑 {a.radius:g} km）\n"
                f"- 固定源/設施：{len(sources)}（上風處 {summary['n_upwind']}）\n- FIRMS 火點：{len(fires)}（疑似工業熱源 {summary['n_fires_industrial']}）\n"
                f"- 新聞線索：{len(news)}（疑似相關 {summary['n_news_relevant']}）\n- 風：{'自%s方 %.0f°，%.1f m/s（%s）' % (compass(wind['dir']), wind['dir'], wind['speed'], '手動' if wind.get('manual') else wind.get('source', '')) if wind else '無資料'}\n"
                + ("".join(f"- ⚠ {x}\n" for x in FAILED) if FAILED else "")
                + (f"\n🗺️ 互動地圖：{os.getenv('MAP_URL')}\n" if os.getenv("MAP_URL")
                   else "\n下載 Artifact 內的 `map.html` 以瀏覽互動地圖。\n"))
    print(json.dumps(summary, ensure_ascii=False))


if __name__ == "__main__":
    main()
