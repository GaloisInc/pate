#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int check_crc(uint16_t crc, void *data) { return (crc == 0); }

int parse_data(void* buffer, uint8_t size, FILE *stream) {
  fread(buffer, size, 1, stream);
  return EXIT_SUCCESS;
}

#define DATA_MAX 64

#define UNEXPECTED_TARGET 1
#define UNEXPECTED_SOURCE 2
#define BAD_SYNC 3
#define BAD_LENGTH 4
#define BAD_CRC 5

#define PROTO_SYNC 0x0564
#define LINK_ACK 0x80
#define PADDING asm("nop");asm("nop");asm("nop");asm("nop");asm("nop");asm("nop");asm("nop");asm("nop");

typedef struct {
  // link layer
  uint16_t sync;
  uint8_t length;
  uint8_t linkControl;
  uint16_t targetAddress;
  uint16_t sourceAddress;
  uint16_t headerCRC;
  // transport layer
  uint8_t transportControl;
  // application layer
  char applicationData[DATA_MAX];
} Packet;

Packet IncomingPacket;

int parse_packet(uint16_t host, uint16_t remote, FILE *stream) {
  // link layer
  fread(&IncomingPacket.sync, 2, 1, stream);
  if (IncomingPacket.sync != PROTO_SYNC) {
    return BAD_SYNC;
  }
  fread(&IncomingPacket.length, 1, 1, stream);
  if (IncomingPacket.length == 0) {
    return BAD_LENGTH;
  }
  fread(&IncomingPacket.linkControl, 1, 1, stream);
  fread(&IncomingPacket.targetAddress, 2, 1, stream);
  if (IncomingPacket.targetAddress != host) {
    return UNEXPECTED_TARGET;
  }
  fread(&IncomingPacket.sourceAddress, 2, 1, stream);
  if (IncomingPacket.sourceAddress != remote) {
    return UNEXPECTED_SOURCE;
  }
  fread(&IncomingPacket.headerCRC, 2, 1, stream);
  if (check_crc(IncomingPacket.headerCRC, &IncomingPacket)) {
    return BAD_CRC;
  }

  // transport layer
  fread(&IncomingPacket.transportControl, 1, 1, stream);
  // application_layer
  uint8_t size = IncomingPacket.length;
  
  if (IncomingPacket.linkControl == LINK_ACK) {
    #ifdef PATCHED
    size = 0;
    #else
    asm("nop");
    asm("nop");
    #endif
  }

  printf("[INFO] Reading %d bytes\n", size);
  return parse_data(&IncomingPacket.applicationData, size, stream);
}

int main(int argc, char **argv) {
  printf("[INFO] Max packet size: %d\n", sizeof(Packet));
  parse_packet(0, 1, NULL);
}