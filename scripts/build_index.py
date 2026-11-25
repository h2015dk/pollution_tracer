#!/usr/bin/env python3
"""產生 GitHub Pages 首頁：列出 site/runs/*/summary.json 的歷次溯源結果（新→舊）。"""
import html
import json
import sys
from pathlib import Path

site = Path(sys.argv[1] if len(sys.argv) > 1 else "site")
rows = []
for f in (site / "runs").glob("*/summary.json"):
    try:
        s = json.loads(f.read_text(encoding="utf-8"))
    except Exception:
        continue
    w = s.get("wind")
    wind = f"{w['dir']:.0f}° {w['speed']:.1f} m/s" if w else "無"
    rows.append((s.get("time", ""), f.parent.name, s, wind))
rows.sort(key=lambda r: r[0], reverse=True)

tr = "".join(
    f"<tr><td><a href='runs/{rid}/map.html'>{html.escape(t[:16].replace('T', ' '))}</a></td>"
    f"<td>{s['lat']}, {s['lon']}</td><td>{s.get('radius_km', '')}</td>"
    f"<td>{html.escape('、'.join(s.get('places', [])[:4]))}</td>"
    f"<td>{s.get('n_sources', '')}（上風 {s.get('n_upwind', '')}）</td><td>{s.get('n_fires', '')}</td>"
    f"<td>{s.get('n_news_relevant', s.get('n_news', ''))}</td><td>{wind}</td>"
    f"<td>{'⚠' if s.get('failed') else ''}</td></tr>"
    for t, rid, s, wind in rows)
(site / "index.html").write_text(f"""<!DOCTYPE html><html lang="zh-Hant"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>污染源溯源紀錄</title>
<style>body{{font:14px/1.5 sans-serif;margin:16px}}table{{border-collapse:collapse;width:100%}}
td,th{{border:1px solid #ccc;padding:4px 6px;white-space:nowrap}}th{{background:#f0f0f0}}
.wrap{{overflow-x:auto}}</style></head><body>
<h2>污染源溯源紀錄</h2><p>點時間開啟互動地圖。⚠＝部分資料查詢失敗（詳見地圖側欄）。</p>
<div class="wrap"><table><tr><th>事件時間</th><th>座標</th><th>半徑km</th><th>行政區</th><th>固定源</th>
<th>火點</th><th>新聞</th><th>風</th><th></th></tr>{tr}</table></div></body></html>""", encoding="utf-8")
print(f"index: {len(rows)} runs")
