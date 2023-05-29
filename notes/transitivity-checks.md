fact {
  all sec : StockSecurity
    | accepted[sec] => issued[sec]
}

fact {
  all sec : StockSecurity
    | cancelled[sec] => accepted[sec]
}

check {
  all sec : StockSecurity
    | cancelled[sec] => issued[sec]
}