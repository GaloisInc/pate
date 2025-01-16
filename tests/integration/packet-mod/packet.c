#include <stdint.h>
#include <stdio.h>
#include "stdlib.h"

int check_crc(uint16_t crc, void *data) { return (crc == 0); }

#define LOG_READ_SIZE 0
#define LOG_READ_RESULT 1
#define LOG_MAX_SIZE 2


#pragma noinline
void log_info(int log_msg, uint8_t value) {
  switch (log_msg) {
    case LOG_MAX_SIZE:
      print("[INFO] Max packet size: ");
      break;
    case LOG_READ_SIZE:
      print("[INFO] Reading bytes: ");
      break;
    case LOG_READ_RESULT:
      print("[INFO] Reading result: ");
      break;
    default:
      print("[UNKNOWN]: ");
  }
  printf("%d\n", value);
}

#pragma noinline
int parse_data(void* buffer, uint8_t* size, FILE *stream) {
  fread(buffer, *size, 1, stream);
  return EXIT_SUCCESS;
}

#pragma noinline
void noop(void* val) {
  return;
}


#define DATA_MAX 64

#define UNEXPECTED_TARGET 1
#define UNEXPECTED_SOURCE 2
#define BAD_SYNC 3
#define BAD_LENGTH 4
#define BAD_CRC 5

#define PROTO_SYNC 0x0564
#define LINK_ACK 0x80

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
int parse_packet(uint16_t host, uint16_t remote, FILE *stream);

int main(int argc, char **argv) {
  log_info(LOG_MAX_SIZE, sizeof(Packet));
  parse_packet(0, 1, NULL);
}

#pragma noinline
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
  void* buffer = &IncomingPacket.applicationData;
  uint8_t ctrl = IncomingPacket.linkControl;

#ifdef BADPATCH
  if (ctrl == LINK_ACK) {
    size = 0;
  }
  log_info(LOG_READ_SIZE, size);
  return parse_data(buffer, size,
                    stream); // passes size int
#elif GOODPATCH
  if (ctrl == LINK_ACK) {
    size = 0;
  }
  log_info(LOG_READ_SIZE, size);
  return parse_data(buffer, &size,
                    stream); // passes size ptr
#else
  asm("nop");
  asm("nop");
  asm("nop");
  asm("nop");
  asm("nop");
  log_info(LOG_READ_SIZE, size);
  return parse_data(buffer, &size,
                    stream);
#endif

}