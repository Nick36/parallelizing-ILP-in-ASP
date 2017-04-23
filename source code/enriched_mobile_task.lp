contact(-1..8).
volume(0).
volume(7).
volume(5).
vibrator(0..2).
battery_level(-1..47).
battery_level(100).
battery_level(71).
battery_level(52).
battery_level(57).
battery_level(69).
screen_brightness(0..1).
light_level(0..1).
battery_charging(0..1).
screen_on(1).
is_charging(1).

% Static Background

high_volume(X) :- volume(X), X > 5.

%low_battery(X) :- battery_level(X), X <= 10.
modeh(low_battery(+battery_level)).
modeb(battery_level_less_or_equal_ten(+battery_level)).
battery_level_less_or_equal_ten(10).
example(low_battery(12),-1).
example(low_battery(10),1).

%high_battery(X) :- battery_level(X), X > 50.
modeh(high_battery(+battery_level)).
modeb(battery_level_greater_than_fifty(+battery_level)).
battery_level_greater_than_fifty(52).
example(high_battery(47),-1).
example(high_battery(52),1).

year(2011).
month(3).
dayofmonth(18..24).
%date((D,M,Y)) :- year(Y), month(M), dayofmonth(D).
modeh(date((+dayofmonth,+month,+year))).
example(date((20,3,2011)),1).

time(0..24).

%morning(H) :- time(H), H < 12, H >= 0.
modeh(morning(+time)).
modeb(time_less_than_twelve(+time)).
time_less_than_twelve(11).
example(morning(12),-1).
example(morning(18),-1).
example(morning(11),1).

%afternoon(H) :- time(H), H >= 12, H < 18.
modeh(afternoon(+time)).
modeb(time_greater_or_equal_twelve(+time)).
time_greater_or_equal_twelve(12).
modeb(time_less_than_eighteen(+time)).
time_less_than_eighteen(12).
example(afternoon(11),-1).
example(afternoon(18),-1).
example(afternoon(12),1).


%evening(H) :- time(H), H >= 18.
modeh(evening(+time)).
modeb(time_greater_or_equal_eighteen(+time)).
time_greater_or_equal_eighteen(18).
example(evening(17),-1).
example(evening(11),-1).
example(evening(18),1).

user_is_using_app((18,3,2011), 18, sms).
user_is_using_app((18,3,2011), 18, googletalk).
user_is_using_app((18,3,2011), 17, googletalk).
user_is_using_app((18,3,2011), 16, googletalk).
user_is_using_app((18,3,2011), 15, googletalk).
user_is_using_app((19,3,2011), 0, googletalk).
user_is_using_app((19,3,2011), 1, googletalk).
user_is_using_app((19,3,2011), 10, googletalk).
user_is_using_app((19,3,2011), 11, googletalk).
user_is_using_app((19,3,2011), 12, googletalk).
user_is_using_app((19,3,2011), 14, googletalk).
user_is_using_app((20,3,2011), 12, googletalk).
user_is_using_app((24,3,2011), 21, googletalk).

app(googletalk).
app(sms).

weekday((18,3,2011)).
weekday((24,3,2011)).

weekend((19,3,2011)).
weekend((20,3,2011)).

example(accept((20,3,2011), 1, 7, 2, 37,1,1,1),-1).
example(accept((20,3,2011), 1, 7, 2, 39,1,1,1),-1).
example(accept((20,3,2011), 1, 7, 2, 44,1,1,1),-1).
example(accept((20,3,2011), 1, 7, 2, 44,1,1,1),-1).
example(accept((19,3,2011), 2, 7, 2, 47,1,0,0),-1).
example(accept((19,3,2011), 5, 7, 2, 22,0,1,1),-1).
example(accept((20,3,2011), 6, 7, 2, 46,1,1,1),-1).
example(accept((18,3,2011), -1, 5, 2, -1,1,1,1),-1).
example(accept((20,3,2011), 3, 7, 2, 13,1,1,1),-1).
example(accept((20,3,2011), 3, 7, 2, 34,0,1,1),-1).
example(accept((20,3,2011), 3, 7, 2, 36,1,1,1),-1).
example(accept((20,3,2011), 3, 7, 2, 42,1,1,1),-1).
example(accept((20,3,2011), 3, 7, 2, 42,1,1,1),-1).
example(accept((20,3,2011), 3, 7, 2, 44,1,1,1),-1).
example(accept((24,3,2011), 3, 0, 0, 100,1,1,1),-1).
example(accept((20,3,2011), 3, 7, 2, 46,1,1,1),-1).
example(accept((18,3,2011), 3, 5, 2, -1,0,0,0),-1).
example(accept((20,3,2011), 4, 7, 2, 10,0,0,0),-1).
example(accept((18,3,2011), 7, 5, 2, -1,1,1,1),-1).

example(accept((18,3,2011), 3, 5, 2, -1,1,0,0),1).
example(accept((19,3,2011), 4, 7, 2, 52,0,0,0),1).
example(accept((19,3,2011), 4, 7, 2, 23,0,0,0),1).
example(accept((19,3,2011), 4, 7, 2, 57,0,1,1),1).
example(accept((20,3,2011), 4, 7, 2, 12,1,1,1),1).
example(accept((20,3,2011), 4, 7, 2, 71,1,1,1),1).
example(accept((20,3,2011), 8, 7, 2, 69,0,1,1),1).

example(busy((20,3,2011), 15, 7, 2, 69,0,1,1),1).

modeh(accept(+date,+contact,+volume,+vibrator,+battery_level,+screen_brightness,+light_level,+battery_charging)).

modeh(busy(+date,+time,+volume,+vibrator,+battery_level,+screen_brightness,+light_level,+battery_charging)).

modeh(accept(+date,#contact,+volume,+vibrator,+battery_level,+screen_brightness,+light_level,+battery_charging)).

modeb(not busy(+date,+time,+volume,+vibrator,+battery_level,+screen_brightness,+light_level,+battery_charging)).

modeh(priority_contact(#contact)).
modeb(priority_contact(+contact)).

modeb(user_is_using_app(+date, +time, #app)).
modeb(not user_is_using_app(+date, +time, #app)).

modeb(high_volume(+volume)).
modeb(not high_volume(+volume)).

modeb(not low_battery(+battery_level)).
modeb(low_battery(+battery_level)).

modeb(not high_battery(+battery_level)).
modeb(high_battery(+battery_level)).

modeb(screen_on(+screen_brightness)).
modeb(not screen_on(+screen_brightness)).

modeb(is_charging(+battery_charging)).
modeb(not is_charging(+battery_charging)).

modeb(morning(+time)).
modeb(afternoon(+time)).
modeb(evening(+time)).

modeb(not morning(+time)).
modeb(not afternoon(+time)).
modeb(not evening(+time)).
