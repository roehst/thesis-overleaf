// Demand side
sig Customer {}

// Supply side
sig Restaurant {
}

sig Menu {
  restaurant : one Restaurant
}

sig Food {
  menu : one Menu,
  categories : set Category
}

abstract sig Category {
  foods : set Food
}

fact {
  ~menus = restaurant
  ~foods = categories
}