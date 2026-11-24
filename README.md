# 污染源溯源資料收集

GitHub → Actions → "Pollution Source Trace" → Run workflow，填入經緯度與時間。
完成後下載 Artifact，開啟 `map.html`。

設定：Settings → Secrets → `FIRMS_MAP_KEY`（NASA FIRMS 免費申請，無則略過火點）。
本機：`pip install -r requirements.txt && python trace.py --lat 25.08 --lon 121.58 --time "2026-11-22 14:00"`
自備固定源：編輯 `data/stationary_sources.csv`（name,lat,lon,category,note）。
