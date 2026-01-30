
# Usar el runtime oficial de AWS Lambda Python
FROM public.ecr.aws/lambda/python:3.12

# Copiar requirements e instalar dependencias
COPY requirements.txt ${LAMBDA_TASK_ROOT}/
RUN pip install --no-cache-dir -r ${LAMBDA_TASK_ROOT}/requirements.txt

# Copiar el código de tu aplicación
COPY . ${LAMBDA_TASK_ROOT}/

# Establecer el handler
CMD ["handler.handler"]