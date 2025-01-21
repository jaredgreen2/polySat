import Egg

example  (h1 : a = b) (h2 : b = c) : a = c :=
  by
  egg [h2,h2]
