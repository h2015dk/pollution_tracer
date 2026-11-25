# 污染源溯源資料收集

GitHub → Actions → "Pollution Source Trace" → Run workflow，填入經緯度與時間。
完成後在該次執行的 Summary 點「互動地圖」網址即可瀏覽（GitHub Pages，免下載）；
歷次紀錄：`https://<帳號>.github.io/pollution_tracer/`。Artifact 仍保留作為備份。

## 首次設定
0. Actions → "Update OSM Taiwan snapshot" → Run workflow（產生 `data/osm_taiwan.csv.gz`，之後每月自動更新）。
   有快照時溯源不需即時查 Overpass；沒有快照才會退回查 Overpass。
1. Settings → Secrets → `FIRMS_MAP_KEY`（NASA FIRMS 免費申請，無則略過火點）。
2. 先跑一次 workflow（會自動建立 `gh-pages` 分支）。
3. Settings → Pages → Source 選「Deploy from a branch」→ Branch `gh-pages` / `(root)` → Save。
   之後每次執行約 1–2 分鐘後網址生效。

⚠ 公開 repo 的 Pages 任何人都看得到，含未公開資料時請勿使用。

本機：`pip install -r requirements.txt && python trace.py --lat 25.08 --lon 121.58 --time "2026-11-22 14:00"`
自備固定源：編輯 `data/stationary_sources.csv`（name,lat,lon,category,note；範例列會自動略過）。
