#!/usr/bin/env python3
"""由 Geofabrik 臺灣 OSM 檔（已先用 osmium tags-filter 篩過）產生本地污染源快照。

用法：python scripts/build_osm_taiwan.py filtered.osm.pbf data/osm_taiwan.csv.gz
輸出欄位：name,category,lat,lon,note（面/線取幾何中心點）
分類規則需與 trace.py 的 OSM_CATEGORIES 一致。
"""
import csv
import gzip
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

import osmium

GEN_SRC = re.compile(r"coal|gas|oil|waste|biomass")
RELIGION = re.compile(r"taoist|buddhist|folk")


def classify(tags, kind):
    g = tags.get
    lu, mm, am = g("landuse"), g("man_made"), g("amenity")
    if lu == "industrial" and kind != "node" or mm == "works":
        return "工業區/工廠"
    if mm in ("chimney", "storage_tank", "flare"):
        return "煙囪/儲槽/燃燒塔"
    if g("power") == "plant" or (g("power") == "generator" and GEN_SRC.search(g("generator:source", ""))):
        return "電廠/發電設施"
    if lu == "landfill" or am == "waste_transfer_station" or mm == "wastewater_plant":
        return "廢棄物/掩埋/污水處理"
    if lu == "quarry" or g("industrial") == "concrete_plant":
        return "砂石/採礦/混凝土"
    if am == "fuel":
        return "加油站(VOC)"
    if am == "crematorium":
        return "殯葬/火化"
    if am == "place_of_worship" and RELIGION.search(g("religion", "")):
        return "廟宇(香燭/金爐/鞭炮/繞境)"
    if lu == "construction":
        return "工地(建案/營建)"
    if g("highway") == "construction" and kind == "way":
        return "道路施工"
    return None


CONSTRUCTION_ZH = {"residential": "住宅", "apartments": "集合住宅", "house": "住宅", "commercial": "商業",
                   "retail": "商場", "office": "辦公", "industrial": "工業/廠房", "school": "學校",
                   "hospital": "醫院", "public": "公共建築", "road": "道路", "motorway": "高速公路",
                   "primary": "主要道路", "secondary": "次要道路", "tertiary": "道路", "railway": "鐵路",
                   "subway": "捷運", "bridge": "橋梁", "station": "車站", "parking": "停車場", "park": "公園"}


def detail(tags):
    """附註：營建類型（OSM construction=*）、業主/營造商等，有標才顯示。"""
    parts = []
    c = tags.get("construction")
    if c:
        parts.append(f"類型:{CONSTRUCTION_ZH.get(c, c)}")
    for k, lab in (("operator", "業主"), ("contractor", "營造"), ("start_date", "開工"),
                   ("opening_date", "預計完工")):
        if tags.get(k):
            parts.append(f"{lab}:{tags[k]}")
    return ("；" + "；".join(parts)) if parts else ""


def name_of(tags):
    return tags.get("name:zh") or tags.get("name") or tags.get("operator") or "(未命名)"


def main(src, dst):
    rows, seen = [], set()
    fp = osmium.FileProcessor(src).with_locations().with_areas()
    for o in fp:
        tags = dict(o.tags)
        if not tags:
            continue
        if o.is_node():
            cat = classify(tags, "node")
            if cat and o.location.valid():
                rows.append((name_of(tags), cat, o.location.lat, o.location.lon, f"osm:node/{o.id}{detail(tags)}"))
        elif o.is_way():
            # 封閉的面狀 way 會再以 area 出現；這裡只處理線（如道路施工）與非封閉 way
            if o.is_closed() and tags.get("highway") != "construction":
                continue
            cat = classify(tags, "way")
            pts = [(n.lat, n.lon) for n in o.nodes if n.location.valid()]
            if cat and pts:
                rows.append((name_of(tags), cat, sum(p[0] for p in pts) / len(pts),
                             sum(p[1] for p in pts) / len(pts), f"osm:way/{o.id}{detail(tags)}"))
        elif o.is_area():
            cat = classify(tags, "area")
            if not cat or cat == "道路施工":
                continue
            pts = [(n.lat, n.lon) for ring in o.outer_rings() for n in ring if n.location.valid()]
            if not pts:
                continue
            oid = f"osm:{'way' if o.from_way() else 'relation'}/{o.orig_id()}"
            if oid in seen:
                continue
            seen.add(oid)
            rows.append((name_of(tags), cat, sum(p[0] for p in pts) / len(pts),
                         sum(p[1] for p in pts) / len(pts), oid + detail(tags)))

    dst = Path(dst)
    dst.parent.mkdir(parents=True, exist_ok=True)
    with gzip.open(dst, "wt", encoding="utf-8", newline="") as f:
        w = csv.writer(f)
        w.writerow(["name", "category", "lat", "lon", "note"])
        for r in rows:
            w.writerow([r[0], r[1], f"{r[2]:.6f}", f"{r[3]:.6f}", r[4]])
    cnt = {}
    for r in rows:
        cnt[r[1]] = cnt.get(r[1], 0) + 1
    meta = dict(built=datetime.now(timezone.utc).isoformat(timespec="minutes"), counts=cnt, total=len(rows))
    dst.with_name("osm_taiwan.meta.json").write_text(json.dumps(meta, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps(meta, ensure_ascii=False))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
