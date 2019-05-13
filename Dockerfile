FROM openjdk:8u212-jdk-stretch
MAINTAINER Futa HIRAKOBA

ENV DEBIAN_FRONTEND noninteractive

RUN apt-get update
RUN apt-get install -y locales

RUN echo "ja_JP.UTF-8 UTF-8" > /etc/locale.gen && \
    locale-gen ja_JP.UTF-8 && \
    dpkg-reconfigure locales && \
    /usr/sbin/update-locale LANG=ja_JP.UTF-8

ENV LC_ALL ja_JP.UTF-8

RUN apt-get install -y g++ make

ADD pict-java /work/pict-java

WORKDIR /work/pict-java/pict

RUN make clean all
RUN mkdir /work/libs && mv libpict.so /work/libs

WORKDIR /work/pict-java

RUN ./gradlew jar