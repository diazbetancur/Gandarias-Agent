# Imagen oficial para Lambda Python 3.12
FROM public.ecr.aws/lambda/python:3.12

# Instala dependencias
COPY requirements.txt .
RUN python -m pip install --no-cache-dir -r requirements.txt

# Copia tu código
COPY agenda.py .
COPY handler.py .

# Handler de Lambda (module.function)
CMD [ "handler.handler" ]
