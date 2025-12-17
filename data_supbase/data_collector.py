# data_collector.py
import sys
import os
import requests
import json
import time
import random 
import csv 
from datetime import datetime, timezone, timedelta
from xml.etree import ElementTree as ET
from requests.exceptions import HTTPError
import math
import psycopg2

# ======================================================
# PHẦN SỬA: KHAI BÁO CẤU HÌNH TRỰC TIẾP (BỎ IMPORT CŨ)
# ======================================================

# 1. API Key (QUAN TRỌNG: Điền key thật của bạn vào trong ngoặc)
OWM_API_KEYS_LIST = [
    "8814cbadb40070726540197edbc5ed82",
    "a07905a6a722d423ac074ec59c6dc56c",
    "41574e5785febeb20b7ec9706ac2960a",
    "fa04a6d7dd10c2c5e5f313961ed9b748",
    "40c1b74868dc5a2187dcea556c138187",
    "4886be21c34791c6d9fe85a481edfe31",
    "4c810aff81a26a9f4fadd2dea2281f29",
    "588f2d0f4434cb5d018d09489e0f441a",
    "ae8ebf9e892fce5ee5eb7276c4bba186",
    "7d0c971c45fc5617ac58eb75b3b34233",
]

# 2. Các hằng số (Trước đây lấy từ config file, giờ khai báo luôn ở đây)
GDACS_URL = "https://www.gdacs.org/Xml/rssarchive.xml"
HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/96.0.4664.110 Safari/537.36"
}

# Danh sách địa điểm mặc định (để trống vì ta sẽ đọc từ file csv)
TARGET_LOCATIONS = [] 

# Tọa độ khung bao Việt Nam (để lọc dữ liệu)
VIETNAM_BBOX = {
    "min_lon": 102.0, "min_lat": 8.0,
    "max_lon": 110.0, "max_lat": 23.5
}

# 3. Hàm log đơn giản
def log(msg):
    print(f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] {msg}")

# 4. Hàm đọc CSV (Giữ nguyên logic của bạn)
def load_locations_from_csv(filename="location.csv"):
    current_dir = os.path.dirname(os.path.abspath(__file__))
    file_path = os.path.join(current_dir, filename)
    locations = []
    if not os.path.exists(file_path): 
        print("⚠️ Không tìm thấy file location.csv, dùng danh sách rỗng.")
        return TARGET_LOCATIONS
    try:
        with open(file_path, mode='r', encoding='utf-8') as f:
            reader = csv.DictReader(f)
            for row in reader:
                try: locations.append({"name": row["name"].strip(), "lat": float(row["lat"]), "lon": float(row["lon"])})
                except ValueError: continue
        log(f"✅ Đã tải {len(locations)} địa điểm từ CSV.")
        return locations
    except Exception as e: 
        print(f"❌ Lỗi đọc CSV: {e}")
        return TARGET_LOCATIONS

# === CẤU HÌNH TIMEZONE ===
try:
    from datetime import UTC as UTC_TZ 
except ImportError:
    from datetime import timezone as _tz
    UTC_TZ = _tz.utc

EARTHQUAKE_RADIUS_KM = 200
EARTHQUAKE_LOOKBACK_DAYS = 365 * 5
EARTHQUAKE_MIN_MAG = 3.0
TC_LOOKBACK_DAYS = 14
TC_PROXIMITY_KM = 800


# PHẦN 1: LOGIC LÀM SẠCH & GÁN NHÃN (LABELING LOGIC)

RISK_ORDER = {"no": 0, "low": 1, "mid": 2, "mid-high": 3, "high": 4}
HAZARD_PRIORITY = ["wind", "rain", "storm", "flood", "earthquake"]

def preprocess_value(val, default=-1.0, precision=2):
    """Làm sạch: None -> default, và làm tròn số."""
    if val is None: return default
    try: return round(float(val), precision)
    except (ValueError, TypeError): return default

def label_rain(p6, p24):
    p6 = max(0, p6); p24 = max(0, p24)
    if p24 > 80 or p6 > 40: return "high"
    if p24 > 50 or p6 > 25: return "mid-high"
    if p24 > 20 or p6 > 10: return "mid"
    if p24 > 3 or p6 > 1: return "low"
    return "no"

def label_wind(gust6):
    gust6 = max(0, gust6)
    if gust6 > 25: return "high"
    if gust6 > 18: return "mid-high"
    if gust6 > 10: return "mid"
    if gust6 > 5: return "low"
    return "no"

def label_storm(gust6, p6, p24, wind, pressure, weather_desc):
    g6 = max(0, gust6); r6 = max(0, p6); r24 = max(0, p24); w = max(0, wind)
    pres = 1013 if pressure == -1.0 else pressure
    score = 0
    
    if g6 > 25: score += 4
    elif g6 > 18: score += 3
    elif g6 > 12: score += 2
    elif g6 > 8: score += 1
    
    if r24 > 80 or r6 > 40: score += 4
    elif r24 > 50 or r6 > 25: score += 3
    elif r24 > 20 or r6 > 10: score += 2
    elif r24 > 3 or r6 > 1: score += 1
    
    if pres < 990: score += 4
    elif pres < 995: score += 3
    elif pres < 1000: score += 2
    
    if "thunderstorm" in str(weather_desc).lower(): score += 2
    elif "heavy" in str(weather_desc).lower(): score += 1

    if score >= 12: return "high"
    if score >= 9: return "mid-high"
    if score >= 6: return "mid"
    if score >= 3: return "low"
    return "no"

def label_flood(river):
    if river == -1.0: return "no"
    if river > 8000: return "high"
    if river > 5000: return "mid-high"
    if river > 2000: return "mid"
    if river > 500: return "low"
    return "no"

def label_earthquake(mag, dist):
    if mag == -1.0 or dist == -1.0: return "no"
    if mag >= 6.0 and dist <= 150: return "high"
    if mag >= 5.5 and dist <= 300: return "mid-high"
    if mag >= 5.0 and dist <= 500: return "mid"
    if mag >= 4.5 and dist <= 800: return "low"
    return "no"

def overall_hazard_prediction(flood, storm, rain, wind, eq):
    risks = {"flood": flood, "storm": storm, "rain": rain, "wind": wind, "earthquake": eq}
    best = "no"; best_score = 0
    for hz in HAZARD_PRIORITY:
        lv = risks[hz]; score = RISK_ORDER[lv]
        if score >= 2: best = hz; best_score = score
    if best_score < 2: return "No"
    return best.capitalize()

# PHẦN 2: CÁC HÀM API & HELPER

def load_locations_from_csv(filename="location.csv"):
    current_dir = os.path.dirname(os.path.abspath(__file__))
    file_path = os.path.join(current_dir, filename)
    locations = []
    if not os.path.exists(file_path): return TARGET_LOCATIONS
    try:
        with open(file_path, mode='r', encoding='utf-8') as f:
            reader = csv.DictReader(f)
            for row in reader:
                try: locations.append({"name": row["name"].strip(), "lat": float(row["lat"]), "lon": float(row["lon"])})
                except ValueError: continue
        log(f"✅ Đã tải {len(locations)} địa điểm từ CSV.")
        return locations
    except Exception: return TARGET_LOCATIONS

def save_to_flat_csv(flat_data_list, filename="vietnam_weather_nowcast.csv"):
    """Lưu danh sách dữ liệu đã xử lý vào CSV theo đúng format yêu cầu."""
    if not flat_data_list: return
    file_exists = os.path.isfile(filename)
    
    # Định nghĩa thứ tự cột (ĐÃ THÊM CỘT TIMESTAMP Ở ĐẦU)
    fieldnames = [
        "timestamp", # <--- CỘT MỚI: THỜI GIAN
        "location", "lat", "lon", 
        "temperature", "humidity", "pressure", "wind_speed", 
        "precip6", "precip24", "gust6", 
        "river_discharge", 
        "eq_mag", "eq_dist", 
        "rain_label", "wind_label", "storm_label", "flood_label", "earthquake_label", 
        "overall_hazard_prediction"
    ]
    
    try:
        with open(filename, mode='a', newline='', encoding='utf-8-sig') as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            if not file_exists:
                writer.writeheader()
            writer.writerows(flat_data_list)
        log(f"✅ [CSV] Đã lưu {len(flat_data_list)} dòng vào '{filename}'.")
    except Exception as e: log(f"❌ [CSV] Lỗi: {e}")

def haversine_km(lat1, lon1, lat2, lon2):
    R = 6371.0; phi1, phi2 = math.radians(lat1), math.radians(lat2); dphi = math.radians(lat2 - lat1); dlambda = math.radians(lon2 - lon1); a = math.sin(dphi / 2) ** 2 + math.cos(phi1) * math.cos(phi2) * math.sin(dlambda / 2) ** 2; return 2 * R * math.asin(math.sqrt(a))
def is_in_vietnam(lat, lon):
    if lat is None or lon is None: return False
    return (VIETNAM_BBOX["min_lat"] <= lat <= VIETNAM_BBOX["max_lat"]) and \
           (VIETNAM_BBOX["min_lon"] <= lon <= VIETNAM_BBOX["max_lon"])

# --- API CALLS ---
def get_openmeteo_nowcast(lat, lon):
    base = "https://api.open-meteo.com/v1/forecast"; params = {"latitude": lat, "longitude": lon, "hourly": "pressure_msl,wind_gusts_10m,precipitation", "wind_speed_unit": "ms", "past_hours": 6, "forecast_hours": 24, "timeformat": "iso8601", "timezone": "UTC"};
    try:
        r = requests.get(base, params=params, timeout=25); j = r.json();
        if r.status_code != 200 or "hourly" not in j: return {}
        H = j["hourly"]; tarr = H.get("time", []); gust = H.get("wind_gusts_10m", []); precip = H.get("precipitation", []); n = len(tarr);
        if n == 0: return {}
        now = datetime.now(UTC_TZ);
        def _to_utc(dtstr): dt = datetime.fromisoformat(dtstr); return dt.replace(tzinfo=UTC_TZ) if dt.tzinfo is None else dt
        times = [_to_utc(t) for t in tarr]; idx_now = max((i for i, t in enumerate(times) if t <= now), default=n-1);
        def _safe_next_slice(i0, step): a, b = i0 + 1, min(i0 + 1 + step, n); return slice(a, b) if a < b else slice(0, 0)
        next6, next24 = _safe_next_slice(idx_now, 6), _safe_next_slice(idx_now, 24);
        return {"gust6": max([x for x in gust[next6] if x is not None], default=None), "p6": sum([x for x in precip[next6] if x is not None], start=0.0) if next6.start < next6.stop else None, "p24": sum([x for x in precip[next24] if x is not None], start=0.0) if next24.start < next24.stop else None}
    except Exception: return {}

def get_flood_forecast(lat, lon):
    base = "https://flood-api.open-meteo.com/v1/flood"; params = {"latitude": lat, "longitude": lon, "daily": "river_discharge_max", "forecast_days": 10};
    try:
        r = requests.get(base, params=params, timeout=25); j = r.json();
        arr = j.get("daily", {}).get("river_discharge_max", [])
        return max([x for x in arr if x is not None], default=None)
    except Exception: return None

def get_earthquake_stats(lat, lon):
    end_dt = datetime.now(UTC_TZ); start_dt = end_dt - timedelta(days=EARTHQUAKE_LOOKBACK_DAYS); 
    params = {"format": "geojson", "latitude": lat, "longitude": lon, "maxradiuskm": EARTHQUAKE_RADIUS_KM, "starttime": start_dt.strftime("%Y-%m-%d"), "endtime": end_dt.strftime("%Y-%m-%d"), "minmagnitude": EARTHQUAKE_MIN_MAG, "limit": 20000};
    try:
        r = requests.get("https://earthquake.usgs.gov/fdsnws/event/1/query", params=params, timeout=30); j = r.json();
        feats = j.get("features", []); 
        if not feats: return None, None
        recent = max(feats, key=lambda f: f["properties"].get("time", 0)); 
        min_dist = min([haversine_km(lat, lon, f["geometry"]["coordinates"][1], f["geometry"]["coordinates"][0]) for f in feats])
        return recent["properties"].get("mag"), min_dist
    except Exception: return None, None

def fetch_disaster_data():
    try:
        resp = requests.get(GDACS_URL, headers=HEADERS, timeout=10); resp.raise_for_status(); xml_content = resp.content.decode('utf-8-sig'); root = ET.fromstring(xml_content); namespaces = {'geo': 'http://www.w3.org/2003/01/geo/wgs84_pos#'}; relevant_events = [];
        for item in root.findall(".//item", namespaces):
            title = item.find("title").text if item.find("title") is not None else ""; lat, lon = None, None; geo_point = item.find("geo:Point", namespaces);
            if geo_point is not None: 
                lat = float(geo_point.find("geo:lat", namespaces).text)
                lon = float(geo_point.find("geo:lon", namespaces).text)
            if is_in_vietnam(lat, lon):
                relevant_events.append({"source": "gdacs_rss", "event_type": "disaster", "title": title, "description": item.find("description").text, "event_time": None, "lat": lat, "lon": lon, "raw_data": {}})
        return relevant_events
    except Exception: return []

# =========================================================
# PHẦN 3: XỬ LÝ & ĐÓNG GÓI DỮ LIỆU
# =========================================================
def process_single_location(lat, lon, location_name):
    # 1. EXTRACT (Thu thập)
    current_key = random.choice(OWM_API_KEYS_LIST)
    try:
        owm_url = f"https://api.openweathermap.org/data/2.5/weather?lat={lat}&lon={lon}&appid={current_key}&units=metric&lang=en"
        resp = requests.get(owm_url, timeout=10); resp.raise_for_status(); owm_data = resp.json()
    except Exception as e: 
        log(f"❌ Lỗi OWM {location_name}: {e}. Bỏ qua."); return None

    nowcast_data = get_openmeteo_nowcast(lat, lon)
    river_raw = get_flood_forecast(lat, lon)
    eq_raw = get_earthquake_stats(lat, lon)

    # 2. TRANSFORM (Làm sạch)
    temp = preprocess_value(owm_data.get("main", {}).get("temp"), -99.0, 1)
    hum = preprocess_value(owm_data.get("main", {}).get("humidity"), -1.0, 0)
    pres = preprocess_value(owm_data.get("main", {}).get("pressure"), -1.0, 0)
    wind = preprocess_value(owm_data.get("wind", {}).get("speed"), 0.0)
    weather_desc = owm_data.get("weather", [{}])[0].get("description", "")

    gust6 = preprocess_value(nowcast_data.get("gust6"), 0.0)
    p6 = preprocess_value(nowcast_data.get("p6"), 0.0)
    p24 = preprocess_value(nowcast_data.get("p24"), 0.0)
    river = preprocess_value(river_raw, -1.0)
    
    eq_mag = preprocess_value(eq_raw[0] if eq_raw else None, -1.0)
    eq_dist = preprocess_value(eq_raw[1] if eq_raw else None, -1.0)

    # 3. LABELING (Gán nhãn)
    rain_lb = label_rain(p6, p24)
    wind_lb = label_wind(gust6)
    storm_lb = label_storm(gust6, p6, p24, wind, pres, weather_desc)
    flood_lb = label_flood(river)
    eq_lb = label_earthquake(eq_mag, eq_dist)
    overall_lb = overall_hazard_prediction(flood_lb, storm_lb, rain_lb, wind_lb, eq_lb)

    # 4. LOAD (Đóng gói Dictionary)
    
    # Lấy thời gian hiện tại dạng string đẹp (ISO format hoặc 'YYYY-MM-DD HH:MM:SS')
    current_time_str = datetime.now(UTC_TZ).strftime('%Y-%m-%d %H:%M:%S')

    flat_data = {
        "timestamp": current_time_str, # <--- ĐÃ THÊM CỘT TIMESTAMP
        "location": location_name, "lat": lat, "lon": lon,
        "temperature": temp, "humidity": hum, "pressure": pres, "wind_speed": wind,
        "precip6": p6, "precip24": p24, "gust6": gust6,
        "river_discharge": river,
        "eq_mag": eq_mag, "eq_dist": eq_dist,
        "rain_label": rain_lb, "wind_label": wind_lb, "storm_label": storm_lb,
        "flood_label": flood_lb, "earthquake_label": eq_lb,
        "overall_hazard_prediction": overall_lb
    }
    
    # Tạo data cho DB (tương thích api_receiver)
    db_event = {
        "source": "owm_flat_batch", "event_type": "weather_analytics",
        "title": f"[{overall_lb}] {location_name}",
        "description": f"Risk: {overall_lb}. Temp: {temp}. RainLbl: {rain_lb}",
        "event_time": datetime.now(UTC_TZ), "lat": lat, "lon": lon, "raw_data": flat_data
    }

    return flat_data, db_event


# --- CẤU HÌNH DATABASE SUPABASE (Lấy từ pgAdmin) ---
# --- CẤU HÌNH DATABASE SUPABASE (Lấy từ biến môi trường của Render) ---
# Cách hoạt động: os.getenv("TÊN_BIẾN", "Giá trị mặc định nếu chạy ở local")

DB_HOST = os.getenv("DB_HOST", "aws-1-ap-southeast-1.pooler.supabase.com")
DB_PORT = os.getenv("DB_PORT", "6543")
DB_NAME = os.getenv("DB_NAME", "postgres")
DB_USER = os.getenv("DB_USER", "postgres.nzgxekzvabvxwhiivbza") # User của bạn
DB_PASS = os.getenv("DB_PASS", "12345678") # <--- Điền pass thật vào đây để test trên máy, lên Render nó sẽ tự đè bằng biến môi trường
def push_data_to_supabase(flat_data):
    """
    Hàm này thay thế việc bạn phải Import CSV bằng tay.
    Nó đẩy thẳng 1 dòng dữ liệu mới vào bảng hazard_data.
    """
    try:
        # 1. Kết nối đến Supabase
        conn = psycopg2.connect(
            host=DB_HOST, database=DB_NAME, user=DB_USER, password=DB_PASS, port=DB_PORT
        )
        cur = conn.cursor()

        # 2. Câu lệnh SQL Insert (Khớp 100% với các cột bảng hazard_data)
        sql = """
            INSERT INTO hazard_data (
                "timestamp", location, lat, lon, 
                temperature, humidity, pressure, wind_speed,
                precip6, precip24, gust6, river_discharge,
                eq_mag, eq_dist,
                rain_label, wind_label, storm_label, flood_label, earthquake_label,
                overall_hazard_prediction
            ) VALUES (
                %s, %s, %s, %s, 
                %s, %s, %s, %s, 
                %s, %s, %s, %s, 
                %s, %s, 
                %s, %s, %s, %s, %s, 
                %s
            );
        """

        # 3. Chuẩn bị dữ liệu (mapping từ dictionary flat_data sang tuple)
        # Lưu ý: 'timestamp' trong flat_data đang là string, Postgres sẽ tự hiểu
        values = (
            flat_data["timestamp"], flat_data["location"], flat_data["lat"], flat_data["lon"],
            flat_data["temperature"], flat_data["humidity"], flat_data["pressure"], flat_data["wind_speed"],
            flat_data["precip6"], flat_data["precip24"], flat_data["gust6"], flat_data["river_discharge"],
            flat_data["eq_mag"], flat_data["eq_dist"],
            flat_data["rain_label"], flat_data["wind_label"], flat_data["storm_label"], flat_data["flood_label"], flat_data["earthquake_label"],
            flat_data["overall_hazard_prediction"]
        )

        # 4. Thực thi và lưu
        cur.execute(sql, values)
        conn.commit()
        
        # Đóng kết nối
        cur.close()
        conn.close()
        # print(f"✅ Đã đẩy data {flat_data['location']} lên Cloud thành công.")
        
    except Exception as e:
        print(f"❌ Lỗi đẩy Supabase: {e}")

# *** HÀM MAIN ***
# ... (Phần trên giữ nguyên) ...

# *** HÀM MAIN (ĐÃ SỬA CHO GITHUB ACTIONS) ***
# *** HÀM MAIN (ĐÃ FIX LỖI) ***
def main():
    log("🚀 BẮT ĐẦU CHẠY TRÊN GITHUB ACTIONS...")
    
    # 1. Đọc danh sách địa điểm
    active_locations = load_locations_from_csv("location.csv")
    n_locations = len(active_locations)
    
    # --- PHẦN SỬA LỖI: BỎ CÁC HÀM CŨ GÂY LỖI ---
    # gdacs_events = fetch_disaster_data() 
    # write_events_to_database(gdacs_events) <--- DÒNG NÀY GÂY LỖI NÊN MÌNH ĐÃ COMMENT LẠI
    
    # 2. Thu thập dữ liệu thời tiết từng điểm
    for idx, loc in enumerate(active_locations):
        # In log ra để biết đang chạy đến đâu
        log(f"➡️ Xử lý {idx+1}/{n_locations}: {loc['name']}")
        
        result = process_single_location(loc['lat'], loc['lon'], loc['name'])
        
        if result:
            flat, db_ev = result
            
            # Đẩy lên Supabase (Chỉ giữ lại cái này là quan trọng nhất)
            push_data_to_supabase(flat)
            
            # write_events_to_database([db_ev]) <--- BỎ DÒNG NÀY LUÔN VÌ GÂY LỖI TƯƠNG TỰ
            
    log("✅ ĐÃ HOÀN TẤT TOÀN BỘ. KẾT THÚC.")

if __name__ == "__main__":
    main()
