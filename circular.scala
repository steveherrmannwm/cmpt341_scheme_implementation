
case class A(b : Box[B])

case class B(a : A)

class Box[A] {
  var contents : Option[A] = None
}

val box = new Box[B]()
val a = A(box)
val b = B(a)
box.contents = Some(b)

a
a.b.contents.get
a.b.contents.get.a
a.b.contents.get.a.b
a.b.contents.get.a.b.contents.get.a




// vim: set ts=2 sw=2 et:
