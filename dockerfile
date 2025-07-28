# ───────────────────────────────────────────────
# Imagen ligera de Python 3.12 con dependencias
# ───────────────────────────────────────────────
FROM python:3.12-slim

# 1. Variables de entorno
ENV PYTHONUNBUFFERED=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    PIP_NO_CACHE_DIR=1

# 2. Instalar dependencias del sistema (para psycopg2-binary y ortools)
RUN apt-get update && \
    apt-get install -y --no-install-recommends gcc g++ \
        libpq-dev && \
    apt-get clean && rm -rf /var/lib/apt/lists/*

# 3. Crear directorio de trabajo
WORKDIR /app

# 4. Copiar requirements (opcional)
# COPY requirements.txt .
# RUN pip install -r requirements.txt

# 5. Instalar dependencias directamente
RUN pip install flask flask-cors psycopg2-binary ortools tabulate

# 6. Copiar la aplicación
COPY agenda.py .

# 7. Puerto expuesto
EXPOSE 5000

# 8. Comando de arranque
CMD ["python", "agenda.py"]
