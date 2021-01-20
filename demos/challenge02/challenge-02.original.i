# 1 "challenge-02.original.cpp"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/powerpc64-linux-gnu/include/stdc-predef.h" 1 3
# 1 "<command-line>" 2
# 1 "challenge-02.original.cpp"
# 1 "/usr/lib/gcc-cross/powerpc64-linux-gnu/5/include/stdint.h" 1 3 4
# 9 "/usr/lib/gcc-cross/powerpc64-linux-gnu/5/include/stdint.h" 3 4
# 1 "/usr/powerpc64-linux-gnu/include/stdint.h" 1 3 4
# 25 "/usr/powerpc64-linux-gnu/include/stdint.h" 3 4
# 1 "/usr/powerpc64-linux-gnu/include/features.h" 1 3 4
# 367 "/usr/powerpc64-linux-gnu/include/features.h" 3 4
# 1 "/usr/powerpc64-linux-gnu/include/sys/cdefs.h" 1 3 4
# 410 "/usr/powerpc64-linux-gnu/include/sys/cdefs.h" 3 4
# 1 "/usr/powerpc64-linux-gnu/include/bits/wordsize.h" 1 3 4
# 411 "/usr/powerpc64-linux-gnu/include/sys/cdefs.h" 2 3 4
# 368 "/usr/powerpc64-linux-gnu/include/features.h" 2 3 4
# 391 "/usr/powerpc64-linux-gnu/include/features.h" 3 4
# 1 "/usr/powerpc64-linux-gnu/include/gnu/stubs.h" 1 3 4




# 1 "/usr/powerpc64-linux-gnu/include/bits/wordsize.h" 1 3 4
# 6 "/usr/powerpc64-linux-gnu/include/gnu/stubs.h" 2 3 4





# 1 "/usr/powerpc64-linux-gnu/include/gnu/stubs-64-v1.h" 1 3 4
# 12 "/usr/powerpc64-linux-gnu/include/gnu/stubs.h" 2 3 4
# 392 "/usr/powerpc64-linux-gnu/include/features.h" 2 3 4
# 26 "/usr/powerpc64-linux-gnu/include/stdint.h" 2 3 4
# 1 "/usr/powerpc64-linux-gnu/include/bits/wchar.h" 1 3 4
# 27 "/usr/powerpc64-linux-gnu/include/stdint.h" 2 3 4
# 1 "/usr/powerpc64-linux-gnu/include/bits/wordsize.h" 1 3 4
# 28 "/usr/powerpc64-linux-gnu/include/stdint.h" 2 3 4
# 36 "/usr/powerpc64-linux-gnu/include/stdint.h" 3 4

# 36 "/usr/powerpc64-linux-gnu/include/stdint.h" 3 4
typedef signed char int8_t;
typedef short int int16_t;
typedef int int32_t;

typedef long int int64_t;







typedef unsigned char uint8_t;
typedef unsigned short int uint16_t;

typedef unsigned int uint32_t;



typedef unsigned long int uint64_t;
# 65 "/usr/powerpc64-linux-gnu/include/stdint.h" 3 4
typedef signed char int_least8_t;
typedef short int int_least16_t;
typedef int int_least32_t;

typedef long int int_least64_t;






typedef unsigned char uint_least8_t;
typedef unsigned short int uint_least16_t;
typedef unsigned int uint_least32_t;

typedef unsigned long int uint_least64_t;
# 90 "/usr/powerpc64-linux-gnu/include/stdint.h" 3 4
typedef signed char int_fast8_t;

typedef long int int_fast16_t;
typedef long int int_fast32_t;
typedef long int int_fast64_t;
# 103 "/usr/powerpc64-linux-gnu/include/stdint.h" 3 4
typedef unsigned char uint_fast8_t;

typedef unsigned long int uint_fast16_t;
typedef unsigned long int uint_fast32_t;
typedef unsigned long int uint_fast64_t;
# 119 "/usr/powerpc64-linux-gnu/include/stdint.h" 3 4
typedef long int intptr_t;


typedef unsigned long int uintptr_t;
# 134 "/usr/powerpc64-linux-gnu/include/stdint.h" 3 4
typedef long int intmax_t;
typedef unsigned long int uintmax_t;
# 10 "/usr/lib/gcc-cross/powerpc64-linux-gnu/5/include/stdint.h" 2 3 4
# 2 "challenge-02.original.cpp" 2





# 6 "challenge-02.original.cpp"
typedef struct __TIM_HandleTypeDef
{
} TIM_HandleTypeDef;

class Bumper {
public:

        TIM_HandleTypeDef *hrtc_ref;
        volatile uint32_t *total_time;

        bool outer_left, inner_left, inner_right, outer_right;

        bool prev_brake_state;
        bool brake_state;
        bool flash_lock;
        uint32_t flash_timer;
        int num_flashes;

        bool need_to_signal;
        bool left_lock, right_lock;
        uint32_t signal_timer;
        uint8_t signal;

        Bumper( TIM_HandleTypeDef *hardware_timer, volatile uint32_t *timer );


        inline uint32_t get_time();


        void brake( void );

        void brake_flash( void );

        void turn_signal_routine( void );

        void brake_routine( void );

};

volatile uint32_t second_timer = 0;
void rx_brake_routine();
TIM_HandleTypeDef htim3;
uint8_t buff[8];
Bumper bumper = Bumper( &htim3, &second_timer );

int main(void) {
  rx_brake_routine();
}


Bumper::Bumper( TIM_HandleTypeDef *hardware_timer, volatile uint32_t *timer ) {


        hrtc_ref = hardware_timer;
        total_time = timer;

        outer_left = inner_left = inner_right = outer_right = false;

        prev_brake_state = false;
        brake_state = false;
        flash_lock = false;
        num_flashes = 0;
        flash_timer = 0;

        need_to_signal = false;
        left_lock = right_lock = false;
        signal_timer = 0;
        signal = 0;
}

void rx_brake_routine(){
        int16_t speed_value;
        uint8_t brake_switch;

        speed_value = (buff[3] << 8) + buff[2];
        brake_switch = (buff[4] & 0b00001100) >> 2;

        bumper.brake_state = (brake_switch) ? true : false;


        if (bumper.brake_state) {
                if ((speed_value > 0) && (bumper.prev_brake_state != bumper.brake_state)){
                        bumper.flash_lock = true;
                        bumper.flash_timer = 0;
                }
        }
        else {
                bumper.flash_lock = false;
        }
        bumper.prev_brake_state = bumper.brake_state;
}
