sig einstein.

kind country type.
type norway (country).
type denmark (country).
type england (country).
type german (country).
type sweden (country).

kind beverage type.
type water (beverage).
type tea (beverage).
type milk (beverage).
type coffee (beverage).
type beer (beverage).

kind cigarette type.
type dunhill (cigarette).
type blend (cigarette).
type pallmall (cigarette).
type prince (cigarette).
type bluemaster (cigarette).

kind animal type.
type cat (animal).
type horse (animal).
type bird (animal).
type fish (animal).
type dog (animal).

kind color type.
type yellow (color).
type blue (color).
type red (color).
type green (color).
type white (color).

kind house type.
type house (country -> beverage -> cigarette -> animal -> color -> house).
type member (A -> list A -> o).
type left_of (house -> house -> list house -> o).
type neighbor (house -> house -> list house -> o).
type answer (list house -> o).
