#!/usr/bin/env python3
"""產生全臺搜尋索引（地圖搜尋框使用）：合併環境部列管清單與 OSM 快照，
只保留有名稱或管編的點，輸出精簡 JSON：[[名稱, 類別, 緯度, 經度, 附註], ...]

用法：python scripts/build_search_index.py site/search/index.json
"""
import csv
import gzip
import json
import sys
from pathlib import Path

SRC = [Path("data/moenv_sources.csv.gz"), Path("data/osm_taiwan.csv.gz")]


def main(dst):
    rows, seen = [], set()
    for p in SRC:
        if not p.exists():
            print(f"略過（不存在）：{p}")
            continue
        n = 0
        with gzip.open(p, "rt", encoding="utf-8") as f:
            for r in csv.DictReader(f):
                name, note = r["name"], r.get("note", "")
                if name in ("", "(未命名)") and "管編" not in note:
                    continue
                key = (name, round(float(r["lat"]), 4), round(float(r["lon"]), 4))
                if key in seen:
                    continue
                seen.add(key)
                # OSM 附註只留類型等資訊，去掉 osm:way/123 這種對搜尋無用的編號
                if note.startswith("osm:"):
                    note = note.split("；", 1)[1] if "；" in note else ""
                rows.append([name, r["category"], round(float(r["lat"]), 5), round(float(r["lon"]), 5), note])
                n += 1
        print(f"{p}：{n} 筆")
    dst = Path(dst)
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(json.dumps(rows, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")
    print(f"索引 {len(rows)} 筆，{dst.stat().st_size / 1e6:.1f} MB → {dst}")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "site/search/index.json")
