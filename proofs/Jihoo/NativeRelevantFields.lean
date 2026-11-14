import Jihoo.NativeEnvironmentTyping

namespace Jihoo.NativeKernel.EnvironmentQuantity
open Environment

def relevantFields (data : Bool) : List Field → List Term → Option (List Term)
  | [], [] => some []
  | field :: fields, argument :: arguments => do
      let rest ← relevantFields data fields arguments
      pure (if data && !field.erased then argument :: rest else rest)
  | _, _ => none

end Jihoo.NativeKernel.EnvironmentQuantity
