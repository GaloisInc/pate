#include <stdint.h>

#define LOW false

// mockup for challenge 2 problem
typedef struct __TIM_HandleTypeDef
{
} TIM_HandleTypeDef;

class Bumper {
public:
        // Hardware timer
        TIM_HandleTypeDef *hrtc_ref;
        volatile uint32_t *total_time;
        // Bumper LED States
        bool outer_left, inner_left, inner_right, outer_right;
        // Brake related variables
        bool prev_brake_state;
        bool brake_state;
        bool flash_lock;
        uint32_t flash_timer;
        int num_flashes;
        // Turn Signal related variables
        bool need_to_signal;
        bool left_lock, right_lock;  // used for giving priority to turn signal > brakes
        uint32_t signal_timer;
        uint8_t signal;  // Raw bits transfered over the network

        Bumper( TIM_HandleTypeDef *hardware_timer, volatile uint32_t *timer );

        // Method to shorten HAL Hardware counter call
        inline uint32_t get_time();

        // Turns brake lights on while mindful of locks (flash, right, left lock)
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
        /* Initialize all states to low/false */
        // Hardware timer reference
        hrtc_ref = hardware_timer;
        total_time = timer;
        // Bumper LED States
        outer_left = inner_left = inner_right = outer_right = LOW;
        // Brake related vars
        prev_brake_state = false;
        brake_state = false;
        flash_lock = false;
        num_flashes = 0;
        flash_timer = 0;
        // Turn signal vars
        need_to_signal = false;
        left_lock = right_lock = false;
        signal_timer = 0;
        signal = 0;
}

void rx_brake_routine(){
        uint16_t speed_value;  // vulnerability here
        uint8_t brake_switch;
        // Extract Speed and brake switch from frame
        speed_value  = (buff[3] << 8) + buff[2];  // buf[3] = speed integer, buf[2] = speed decimal
        brake_switch = (buff[4] & 0b00001100) >> 2;
        // update related bumper members
        bumper.brake_state = (brake_switch) ? true : false;

        // This segment would ideally be moved to bumper method
        if (bumper.brake_state) {
                if ((speed_value > 0) && (bumper.prev_brake_state != bumper.brake_state)){  // speed > 0 and brakes were off last
                        bumper.flash_lock = true;
                        bumper.flash_timer = 0;
                }
        }
        else {
                bumper.flash_lock = false;
        }
        bumper.prev_brake_state = bumper.brake_state;
}


