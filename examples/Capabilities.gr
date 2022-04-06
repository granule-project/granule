-- console log
helloWorld : () [{Console}] -> ()
helloWorld x = (cap Console x) "Hello world"

sayTime : () [{TimeDate, Console}] -> ()
sayTime [x] = cap Console [x] ((cap TimeDate [x]) ())

main : () <>
main = let () = helloWorld [()] in pure (sayTime [()])