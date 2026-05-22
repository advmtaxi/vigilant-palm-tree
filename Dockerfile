FROM node:20

WORKDIR /app

# copy package files first (better caching)
COPY package*.json ./

RUN npm install

# copy your server
COPY . .

EXPOSE 7860

CMD ["node", "server.js"]
