# app.py —— 修订版 v1.6.2
# 修复：chart_points 生效、参数持久化、添加10m周期、暂无问题

from flask import Flask, render_template, jsonify, request
from apscheduler.schedulers.background import BackgroundScheduler
import requests
import time
import uuid
import threading
import math
import json
import os
from datetime import datetime
from bisect import bisect_right
from concurrent.futures import ThreadPoolExecutor, as_completed

app = Flask(__name__)

VERSION = "v1.6.2"

# ─────────────────────────────────────────────
# 代理配置（优先读环境变量）
# ─────────────────────────────────────────────
PROXY_HOST = os.getenv("PROXY_HOST", "127.0.0.1")
PROXY_PORT = int(os.getenv("PROXY_PORT", 7897))
PROXY_URL  = f"http://{PROXY_HOST}:{PROXY_PORT}" if PROXY_HOST else None

SETTINGS_FILE = "settings.json"

# ─────────────────────────────────────────────
# 图表周期配置（新增 10m）
# ─────────────────────────────────────────────
CHART_PERIODS = {
    "1m":  1,
    "3m":  3,
    "5m":  5,
    "10m": 10,   # ← 新增
    "15m": 15,
    "30m": 30,
    "1h":  60,
    "2h":  120,
    "4h":  240,
    "1d":  1440,
}

# Binance K线 interval 字符串映射（新增 10m）
CHART_KLINE_INTERVAL = {
    "1m":  "1m",
    "3m":  "3m",
    "5m":  "5m",
    "10m": "1m",   # ← Binance 无 10m，用 1m 拉后取每10根末条；这里直接用 "1m" 多拉点数
    "15m": "15m",
    "30m": "30m",
    "1h":  "1h",
    "2h":  "2h",
    "4h":  "4h",
    "1d":  "1d",
}

# K线缓存 TTL（秒）
SPARKLINE_CACHE_TTL = {
    "1m":  15,
    "3m":  30,
    "5m":  45,
    "10m": 60,
    "15m": 90,
    "30m": 180,
    "1h":  360,
    "2h":  720,
    "4h":  1500,
    "1d":  3600,
}

# ─────────────────────────────────────────────
# 默认配置（新增 chart_points）
# ─────────────────────────────────────────────
DEFAULT_CONFIG = {
    "refresh_interval": 5,
    "time_window":      60,
    "top_n":            20,
    "min_volume":       0,
    "rise_threshold":   3.0,
    "drop_threshold":   -3.0,
    "alert_enabled":    False,
    "chart_enabled":    False,
    "chart_period":     "15m",
    "chart_points":     48,    # ← 新增：K线显示点数
}

START_TIME             = time.time()
MAX_HISTORY_MINUTES    = 1500
ALERT_COOLDOWN_SECONDS = 300


# ─────────────────────────────────────────────
# 配置持久化
# ─────────────────────────────────────────────
def normalize_config_value(key, value):
    if key == "refresh_interval":
        return max(1, int(float(value)))
    if key == "time_window":
        return max(1, min(1440, int(float(value))))
    if key == "top_n":
        return max(5, min(200, int(float(value))))
    if key == "min_volume":
        return max(0.0, float(value))
    if key in ("rise_threshold", "drop_threshold"):
        return float(value)
    if key == "alert_enabled":
        return bool(value)
    if key == "chart_enabled":
        return bool(value)
    if key == "chart_period":
        return value if value in CHART_PERIODS else "15m"
    if key == "chart_points":                          # ← 新增
        return max(10, min(500, int(float(value))))
    return value


def load_config_from_file():
    if not os.path.exists(SETTINGS_FILE):
        return DEFAULT_CONFIG.copy()
    try:
        with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        cfg = DEFAULT_CONFIG.copy()
        for k in cfg:
            if k in data:
                cfg[k] = normalize_config_value(k, data[k])
        return cfg
    except Exception as e:
        print(f"[CONFIG] 读取失败，使用默认值: {e}")
        return DEFAULT_CONFIG.copy()


def save_config_to_file():
    try:
        with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
            json.dump(CONFIG, f, ensure_ascii=False, indent=2)
    except Exception as e:
        print(f"[CONFIG] 保存失败: {e}")


CONFIG = load_config_from_file()

# ─────────────────────────────────────────────
# 全局状态与锁
# ─────────────────────────────────────────────
CACHE_LOCK = threading.Lock()
CACHE = {
    "tickers":             [],
    "last_update":         None,
    "alerts":              [],
    "is_updating":         False,
    "error":               None,
    "data_source":         "REST轮询 + K线回看",
    "needs_bootstrap":     True,
    "bootstrapped_window": None,
    "update_counter":      0,
}

# 最新价格表：symbol -> {price, quote_volume, change24h, time}
LATEST_PRICES = {}
LATEST_LOCK   = threading.Lock()

# 逐分钟历史：symbol -> List[{bucket, time, price}]
PRICE_HISTORY = {}
HISTORY_LOCK  = threading.Lock()

# 告警冷却：symbol -> timestamp
ALERT_COOLDOWN      = {}
ALERT_COOLDOWN_LOCK = threading.Lock()

# K线 sparkline 缓存：symbol -> {period -> {fetch_time, data}}
SPARKLINE_KLINE_CACHE      = {}
SPARKLINE_KLINE_CACHE_LOCK = threading.Lock()

# bootstrap 并发控制
_bootstrap_event = threading.Event()
_bootstrap_event.set()


# ─────────────────────────────────────────────
# HTTP Session
# ─────────────────────────────────────────────
SESSION = requests.Session()
SESSION.headers.update({
    "Accept-Encoding": "gzip",
    "User-Agent":      "Mozilla/5.0",
})
if PROXY_URL:
    SESSION.proxies = {"http": PROXY_URL, "https": PROXY_URL}

_adapter = requests.adapters.HTTPAdapter(
    pool_connections=4,
    pool_maxsize=20,
    max_retries=requests.adapters.Retry(total=2, backoff_factor=0.5),
)
SESSION.mount("https://", _adapter)
SESSION.mount("http://",  _adapter)

scheduler = None


# ─────────────────────────────────────────────
# CACHE 工具函数
# ─────────────────────────────────────────────
def cache_get(key):
    with CACHE_LOCK:
        return CACHE[key]


def cache_set(**kwargs):
    with CACHE_LOCK:
        CACHE.update(kwargs)


# ─────────────────────────────────────────────
# 工具：时间窗口 -> K线参数（用于 bootstrap）
# ─────────────────────────────────────────────
def get_window_params(minutes):
    if minutes <= 60:
        return "1m", 1, minutes + 1
    elif minutes <= 300:
        return "5m", 5, math.ceil(minutes / 5) + 1
    elif minutes <= 720:
        return "15m", 15, math.ceil(minutes / 15) + 1
    elif minutes <= 1440:
        return "1h", 60, math.ceil(minutes / 60) + 1
    else:
        return "4h", 240, math.ceil(minutes / 240) + 1


# ─────────────────────────────────────────────
# 行情快照拉取
# ─────────────────────────────────────────────
def load_market_snapshot():
    """拉取全量 24hr ticker，返回只含 USDT 合约的列表。"""
    url = "https://fapi.binance.com/fapi/v1/ticker/24hr"
    try:
        resp = SESSION.get(url, timeout=15)
        resp.raise_for_status()
        raw = resp.json()

        items = []
        for item in raw:
            symbol = item.get("symbol", "")
            if not symbol.endswith("USDT"):
                continue
            try:
                price = float(item.get("lastPrice") or 0)
                if price <= 0:
                    continue
                items.append({
                    "symbol":       symbol,
                    "price":        price,
                    "quote_volume": float(item.get("quoteVolume") or 0),
                    "change24h":    float(item.get("priceChangePercent") or 0),
                })
            except Exception:
                continue

        cache_set(error=None)
        return items

    except Exception as e:
        msg = f"行情拉取失败：{e}"
        cache_set(error=msg)
        print(f"[REST] {msg}")
        return []


# ─────────────────────────────────────────────
# 历史写入（逐分钟 bucket）
# ─────────────────────────────────────────────
def _upsert_history(symbol, price):
    now           = time.time()
    minute_bucket = int(now // 60)

    with HISTORY_LOCK:
        hist = PRICE_HISTORY.setdefault(symbol, [])
        if hist and hist[-1]["bucket"] == minute_bucket:
            hist[-1]["price"] = price
            hist[-1]["time"]  = now
        else:
            hist.append({"bucket": minute_bucket, "time": now, "price": price})
            if len(hist) > MAX_HISTORY_MINUTES + 10:
                del hist[:len(hist) - (MAX_HISTORY_MINUTES + 5)]


# ─────────────────────────────────────────────
# 原子替换最新价格表
# ─────────────────────────────────────────────
def _update_latest_prices(snapshot):
    ts = time.time()
    new_prices = {
        item["symbol"]: {
            "price":        item["price"],
            "quote_volume": item["quote_volume"],
            "change24h":    item["change24h"],
            "time":         ts,
        }
        for item in snapshot
    }
    with LATEST_LOCK:
        LATEST_PRICES.clear()
        LATEST_PRICES.update(new_prices)


# ─────────────────────────────────────────────
# Bootstrap（历史 K 线回补）
# ─────────────────────────────────────────────
def _bootstrap_worker(snapshot_items, window_minutes):
    if not _bootstrap_event.is_set():
        print("[BOOT] 已有 bootstrap 在运行，跳过")
        return

    _bootstrap_event.clear()
    try:
        interval, interval_minutes, limit = get_window_params(window_minutes)
        end_time_ms = int(time.time() * 1000)
        total       = len(snapshot_items)

        print(f"[BOOT] 开始：窗口 {window_minutes}m → {interval} x {limit} 根，共 {total} 合约")

        with HISTORY_LOCK:
            PRICE_HISTORY.clear()

        failed = 0

        def fetch_one(item):
            symbol = item["symbol"]
            try:
                resp = SESSION.get(
                    "https://fapi.binance.com/fapi/v1/klines",
                    params={
                        "symbol":   symbol,
                        "interval": interval,
                        "limit":    limit,
                        "endTime":  end_time_ms,
                    },
                    timeout=12,
                )
                resp.raise_for_status()
                hist = [
                    {
                        "bucket": int(float(k[6]) / 1000 // 60),
                        "time":   float(k[6]) / 1000,
                        "price":  float(k[4]),
                    }
                    for k in resp.json()
                ]
                return symbol, hist, None
            except requests.Timeout:
                return symbol, [], "timeout"
            except Exception as e:
                return symbol, [], str(e)

        max_workers = min(20, max(4, total // 15))
        done        = 0

        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = {executor.submit(fetch_one, item): item for item in snapshot_items}
            for f in as_completed(futures):
                symbol, hist, err = f.result()
                done += 1
                if done % 100 == 0:
                    print(f"[BOOT] 进度: {done}/{total}")
                if err:
                    failed += 1
                elif hist:
                    with HISTORY_LOCK:
                        PRICE_HISTORY[symbol] = hist[-(MAX_HISTORY_MINUTES + 5):]

        cache_set(bootstrapped_window=window_minutes, needs_bootstrap=False)
        print(f"[BOOT] 完成：{total} 合约，失败 {failed} 个")
        _do_build_and_store()

    except Exception as e:
        print(f"[BOOT] 意外错误: {e}")
        cache_set(error=f"bootstrap 失败：{e}")
    finally:
        _bootstrap_event.set()


# ─────────────────────────────────────────────
# 变化率计算
# ─────────────────────────────────────────────
def calculate_change(symbol, window_minutes):
    with LATEST_LOCK:
        latest = LATEST_PRICES.get(symbol)
    if not latest:
        return 0.0

    if window_minutes >= 1440:
        return round(float(latest.get("change24h", 0.0)), 2)

    with HISTORY_LOCK:
        hist = list(PRICE_HISTORY.get(symbol, []))
    if not hist:
        return 0.0

    now_bucket    = int(time.time() // 60)
    cutoff_bucket = now_bucket - window_minutes

    buckets   = [x["bucket"] for x in hist]
    idx       = bisect_right(buckets, cutoff_bucket) - 1
    old_price = hist[0]["price"] if idx < 0 else hist[idx]["price"]

    current_price = hist[-1]["price"]
    if old_price <= 0:
        return 0.0
    return round((current_price - old_price) / old_price * 100, 2)


# ─────────────────────────────────────────────
# Sparkline：直接拉 Binance K线（带TTL缓存）
# ─────────────────────────────────────────────
def fetch_kline_sparkline(symbol, chart_period="15m", num_points=None):
    """
    直接从 Binance 拉取指定周期的 K线收盘价序列。

    10m 周期特殊处理：Binance 无 10m interval，
    改用 1m K线拉 num_points*10 根，然后每10根取最后一根收盘价做采样。
    """
    if num_points is None:
        num_points = CONFIG.get("chart_points", 48)   # ← 用配置值，不再硬编码

    ttl = SPARKLINE_CACHE_TTL.get(chart_period, 60)
    now = time.time()

    # 检查 TTL 缓存（缓存 key 包含 num_points，避免点数变更后读旧缓存）
    cache_key = f"{chart_period}_{num_points}"
    with SPARKLINE_KLINE_CACHE_LOCK:
        sym_cache = SPARKLINE_KLINE_CACHE.get(symbol, {})
        cached    = sym_cache.get(cache_key)
        if cached and (now - cached["fetch_time"]) < ttl:
            return cached["data"]

    closes = []
    try:
        if chart_period == "10m":
            # 10m 特殊：拉 1m，每10根采样一个
            fetch_limit = min(num_points * 10, 1000)
            resp = SESSION.get(
                "https://fapi.binance.com/fapi/v1/klines",
                params={"symbol": symbol, "interval": "1m", "limit": fetch_limit},
                timeout=8,
            )
            resp.raise_for_status()
            raw = resp.json()
            # 每 10 根取最后一根的收盘价
            closes = [float(raw[i][4]) for i in range(9, len(raw), 10)]
            # 保证最多 num_points 个点
            closes = closes[-num_points:]
        else:
            interval = CHART_KLINE_INTERVAL.get(chart_period, "15m")
            resp = SESSION.get(
                "https://fapi.binance.com/fapi/v1/klines",
                params={"symbol": symbol, "interval": interval, "limit": num_points},
                timeout=8,
            )
            resp.raise_for_status()
            closes = [float(k[4]) for k in resp.json()]

    except requests.Timeout:
        print(f"[KLINE] {symbol} {chart_period} 超时")
    except Exception as e:
        print(f"[KLINE] {symbol} {chart_period} 失败: {e}")

    # 写缓存
    with SPARKLINE_KLINE_CACHE_LOCK:
        if symbol not in SPARKLINE_KLINE_CACHE:
            SPARKLINE_KLINE_CACHE[symbol] = {}
        SPARKLINE_KLINE_CACHE[symbol][cache_key] = {
            "fetch_time": now,
            "data":       closes,
        }

    return closes


# ─────────────────────────────────────────────
# 排名构建
# ─────────────────────────────────────────────
def build_ranking(update_counter):
    with LATEST_LOCK:
        prices = dict(LATEST_PRICES)
    if not prices:
        return []

    window        = CONFIG["time_window"]
    chart_enabled = CONFIG["chart_enabled"]
    chart_period  = CONFIG["chart_period"]
    chart_points  = CONFIG.get("chart_points", 48)   # ← 读配置
    min_volume    = CONFIG["min_volume"]
    top_n         = CONFIG["top_n"]

    results = []
    for symbol, info in prices.items():
        if not symbol.endswith("USDT"):
            continue
        if info["quote_volume"] < min_volume:
            continue

        change = calculate_change(symbol, window)
        results.append({
            "symbol":    symbol.replace("USDT", "/USDT"),
            "_symbol":   symbol,
            "price":     info["price"],
            "change":    change,
            "change24h": round(info["change24h"], 2),
            "volume":    round(info["quote_volume"] / 1_000_000, 2),
        })

    results.sort(key=lambda x: x["change"], reverse=True)

    if chart_enabled:
        # 对所有币都拉K线，不限top/bottom N。
        # TTL 缓存（10s~3600s）确保不会过度请求 Binance API。
        def fetch_for(item):
            sym = item["_symbol"]
            item["sparkline"] = fetch_kline_sparkline(sym, chart_period, chart_points)
            return item

        with ThreadPoolExecutor(max_workers=20) as ex:
            results = list(ex.map(fetch_for, results))

    for item in results:
        item.pop("_symbol", None)

    return results


# ─────────────────────────────────────────────
# 告警检测
# ─────────────────────────────────────────────
def check_alerts(tickers):
    now_ts     = time.time()
    now_str    = datetime.now().strftime("%H:%M:%S")
    new_alerts = []

    for item in tickers:
        sym = item["symbol"]

        with ALERT_COOLDOWN_LOCK:
            last_time = ALERT_COOLDOWN.get(sym, 0)
            if now_ts - last_time < ALERT_COOLDOWN_SECONDS:
                continue

        alert_type = None
        if item["change"] >= CONFIG["rise_threshold"]:
            alert_type = "rise"
        elif item["change"] <= CONFIG["drop_threshold"]:
            alert_type = "drop"

        if alert_type:
            with ALERT_COOLDOWN_LOCK:
                ALERT_COOLDOWN[sym] = now_ts
            new_alerts.append({
                "id":     str(uuid.uuid4()),
                "time":   now_str,
                "symbol": sym,
                "change": item["change"],
                "price":  item["price"],
                "type":   alert_type,
            })

    if new_alerts:
        with CACHE_LOCK:
            CACHE["alerts"].extend(new_alerts)
            CACHE["alerts"] = CACHE["alerts"][-100:]


# ─────────────────────────────────────────────
# 构建排名并写回 CACHE
# ─────────────────────────────────────────────
def _do_build_and_store():
    with CACHE_LOCK:
        counter = CACHE["update_counter"] + 1

    results = build_ranking(counter)
    if not results:
        return

    if CONFIG["alert_enabled"]:
        check_alerts(results)

    now_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    with CACHE_LOCK:
        CACHE["tickers"]        = results
        CACHE["last_update"]    = now_str
        CACHE["data_source"]    = "REST轮询 + K线回看"
        CACHE["update_counter"] = counter

    print(f"[{now_str}] 排名更新，{len(results)} 合约")


# ─────────────────────────────────────────────
# 主刷新入口
# ─────────────────────────────────────────────
def refresh_now():
    with CACHE_LOCK:
        if CACHE["is_updating"]:
            return
        CACHE["is_updating"] = True

    start = time.time()
    try:
        snapshot = load_market_snapshot()
        if not snapshot:
            print("⚠️ 行情快照为空，跳过本轮")
            return

        window = CONFIG["time_window"]

        with CACHE_LOCK:
            needs_boot = CACHE["needs_bootstrap"]
            booted_win = CACHE["bootstrapped_window"]

        if window < 1440 and (needs_boot or booted_win != window):
            _update_latest_prices(snapshot)
            for item in snapshot:
                _upsert_history(item["symbol"], item["price"])
            threading.Thread(
                target=_bootstrap_worker,
                args=(snapshot, window),
                daemon=True,
                name="bootstrap-thread",
            ).start()
            print(f"[REFRESH] bootstrap 已启动，本轮跳过排名构建")
            return

        _update_latest_prices(snapshot)
        for item in snapshot:
            _upsert_history(item["symbol"], item["price"])

        if window >= 1440:
            cache_set(bootstrapped_window=1440, needs_bootstrap=False)

        _do_build_and_store()

        elapsed = round(time.time() - start, 1)
        print(f"[REFRESH] 完成，耗时 {elapsed}s")

    except Exception as e:
        err = str(e)
        cache_set(error=err)
        print(f"[ERROR] refresh_now: {err}")
    finally:
        cache_set(is_updating=False)


# ─────────────────────────────────────────────
# Flask 路由
# ─────────────────────────────────────────────
@app.route("/")
def index():
    return render_template("index.html")


@app.route("/api/tickers")
def api_tickers():
    top_n = CONFIG["top_n"]

    with CACHE_LOCK:
        tickers       = list(CACHE["tickers"])
        last_update   = CACHE["last_update"]
        alerts        = list(CACHE["alerts"][-20:])
        is_updating   = CACHE["is_updating"]
        error         = CACHE["error"]
        data_source   = CACHE["data_source"]
        booted_window = CACHE["bootstrapped_window"]
        update_ctr    = CACHE["update_counter"]

    bottom = tickers[-top_n:][::-1] if len(tickers) >= top_n else tickers[::-1]

    return jsonify({
        "version":             VERSION,
        "all_tickers":         tickers,
        "tickers":             tickers[:top_n],
        "bottom":              bottom,
        "last_update":         last_update,
        "config":              CONFIG,
        "alerts":              alerts,
        "total":               len(tickers),
        "is_updating":         is_updating,
        "error":               error,
        "data_source":         data_source,
        "bootstrapped_window": booted_window,
        "update_counter":      update_ctr,
        "chart_periods":       list(CHART_PERIODS.keys()),
    })


@app.route("/api/config", methods=["POST"])
def update_config():
    global scheduler
    data       = request.json or {}
    old_window = CONFIG["time_window"]
    old_period = CONFIG["chart_period"]

    for key, value in data.items():
        if key in CONFIG:
            CONFIG[key] = normalize_config_value(key, value)

    if CONFIG["time_window"] != old_window:
        cache_set(needs_bootstrap=True, bootstrapped_window=None)

    # 图表周期或点数变更时清空旧 K线缓存
    if CONFIG["chart_period"] != old_period:
        with SPARKLINE_KLINE_CACHE_LOCK:
            for sym_cache in SPARKLINE_KLINE_CACHE.values():
                # 清掉旧周期所有 cache_key（前缀匹配）
                keys_to_del = [k for k in sym_cache if k.startswith(old_period + "_")]
                for k in keys_to_del:
                    del sym_cache[k]

    save_config_to_file()

    if scheduler:
        scheduler.remove_all_jobs()
        scheduler.add_job(
            refresh_now, "interval",
            seconds=CONFIG["refresh_interval"],
            id="refresh_job", max_instances=1,
        )

    return jsonify({"status": "ok", "config": CONFIG})


@app.route("/api/refresh", methods=["POST"])
def manual_refresh():
    threading.Thread(target=refresh_now, daemon=True).start()
    return jsonify({"status": "ok"})


@app.route("/api/alerts/<alert_id>", methods=["DELETE"])
def delete_alert(alert_id):
    with CACHE_LOCK:
        before          = len(CACHE["alerts"])
        CACHE["alerts"] = [a for a in CACHE["alerts"] if a["id"] != alert_id]
        deleted         = before - len(CACHE["alerts"])
    return jsonify({"status": "ok", "deleted": deleted})


@app.route("/api/alerts/clear", methods=["POST"])
def clear_alerts():
    with CACHE_LOCK:
        CACHE["alerts"] = []
    return jsonify({"status": "ok"})


@app.route("/api/health")
def health():
    with CACHE_LOCK:
        booted     = not CACHE["needs_bootstrap"]
        is_booting = not _bootstrap_event.is_set()

    with HISTORY_LOCK:
        history_count = len(PRICE_HISTORY)

    with LATEST_LOCK:
        symbol_count = len(LATEST_PRICES)

    with SPARKLINE_KLINE_CACHE_LOCK:
        kline_cache_count = sum(len(v) for v in SPARKLINE_KLINE_CACHE.values())

    return jsonify({
        "status":              "ok",
        "version":             VERSION,
        "uptime":              round(time.time() - START_TIME),
        "symbols":             symbol_count,
        "history":             history_count,
        "bootstrapped":        booted,
        "bootstrapping":       is_booting,
        "scheduler":           scheduler.running if scheduler else False,
        "proxy":               PROXY_URL or "disabled",
        "kline_cache_entries": kline_cache_count,
        "chart_points":        CONFIG.get("chart_points", 48),
    })


# ─────────────────────────────────────────────
# 启动
# ─────────────────────────────────────────────
if __name__ == "__main__":
    scheduler = BackgroundScheduler(
        job_defaults={"max_instances": 1, "misfire_grace_time": 10}
    )
    scheduler.add_job(
        refresh_now, "interval",
        seconds=CONFIG["refresh_interval"],
        id="refresh_job", max_instances=1,
        next_run_time=datetime.now(),
    )
    scheduler.start()
    app.run(debug=False, port=5000, use_reloader=False, threaded=True)