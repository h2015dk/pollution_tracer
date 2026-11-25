#!/usr/bin/env python3
"""下載環境部「環境保護許可管理系統(暨解除列管)對象基本資料」(EMS_S_01)，
篩出目前空污列管（IsAir 為是、且未空解列）的公私場所，輸出 data/moenv_sources.csv.gz。

用法：MOENV_API_KEY=... python scripts/build_moenv_sources.py data/moenv_sources.csv.gz
"""
import csv
import gzip
import json
import os
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import requests

API = "https://data.moenv.gov.tw/api/v2/ems_s_01"
PAGE = 1000
YES = {"Y", "y", "是", "1", "TRUE", "True", "true", "V", "v"}


def pick(rec, *names):
    low = {k.lower(): v for k, v in rec.items()}
    for n in names:
        v = low.get(n.lower())
        if v not in (None, ""):
            return str(v).strip()
    return ""


def fetch_all(key):
    rows, offset = [], 0
    while True:
        for i in range(4):
            try:
                r = requests.get(API, params=dict(api_key=key, format="JSON", limit=PAGE, offset=offset),
                                 timeout=120)
                r.raise_for_status()
                js = r.json()
                break
            except Exception as e:
                print(f"offset={offset} 第 {i + 1} 次失敗：{e}", file=sys.stderr)
                time.sleep(15 * (i + 1))
        else:
            raise SystemExit("EMS_S_01 下載失敗")
        recs = js.get("records", js) if isinstance(js, dict) else js
        if not isinstance(recs, list):
            raise SystemExit(f"非預期回傳：{str(js)[:300]}")
        if offset == 0:
            print(f"欄位：{list(recs[0].keys()) if recs else '（無資料）'}；total={js.get('total') if isinstance(js, dict) else '?'}")
        rows += recs
        if len(recs) < PAGE:
            return rows
        offset += PAGE
        time.sleep(1)


def main(dst):
    key = os.getenv("MOENV_API_KEY", "").strip()
    if not key:
        raise SystemExit("未設定 MOENV_API_KEY")
    recs = fetch_all(key)
    isair_vals = {}
    out = []
    for r in recs:
        ia = pick(r, "IsAir")
        isair_vals[ia] = isair_vals.get(ia, 0) + 1
        if ia not in YES or pick(r, "AirReleaseDate"):
            continue
        try:
            lat, lon = float(pick(r, "WGS84Lat")), float(pick(r, "WGS84Lon"))
        except ValueError:
            continue
        if not (21.5 < lat < 26.5 and 118 < lon < 122.5):
            continue
        note = "；".join(x for x in [
            f"管編:{pick(r, 'EmsNo')}",
            f"行業:{pick(r, 'IndustryName')}" if pick(r, "IndustryName") else "",
            f"工業區:{pick(r, 'IndustryAreaName')}" if pick(r, "IndustryAreaName") else "",
            pick(r, "FacilityAddress")] if x)
        out.append([pick(r, "FacilityName") or "(未命名)", "空污列管公私場所", f"{lat:.6f}", f"{lon:.6f}", note])
    print(f"IsAir 值分布：{isair_vals}")
    print(f"全部 {len(recs)} 筆 → 空污列管且有座標 {len(out)} 筆")
    if not out:
        raise SystemExit("篩選後 0 筆，請檢查 IsAir 值分布（上方）")
    dst = Path(dst)
    dst.parent.mkdir(parents=True, exist_ok=True)
    with gzip.open(dst, "wt", encoding="utf-8", newline="") as f:
        w = csv.writer(f)
        w.writerow(["name", "category", "lat", "lon", "note"])
        w.writerows(out)
    meta = dict(built=datetime.now(timezone.utc).isoformat(timespec="minutes"), source="環境部 EMS_S_01",
                total_records=len(recs), air_listed=len(out))
    dst.with_name("moenv_sources.meta.json").write_text(json.dumps(meta, ensure_ascii=False, indent=2),
                                                        encoding="utf-8")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "data/moenv_sources.csv.gz")
