/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons01
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core029 : Family 5 := level5.get ⟨19,by decide⟩
def sourceMap029 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 5 2 2 v)
def fusedMap029 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap029_checked : acceptsGraphIso
    (source (graph core029) (root 5) 2 2) SmallGeFourSpectrum196.graph
      sourceMap029=true := by decide +kernel
theorem fusedMap029_checked : acceptsGraphIso
    (fused (graph core029) (root 5) 2 2) SmallGeFourSpectrum093.graph
      fusedMap029=true := by decide +kernel
theorem certified029 : Certified (graph core029) (root 5) 2 2 :=
  of_native_maps core029 SmallGeFourSpectrum196.graph SmallGeFourSpectrum093.graph
    sourceMap029 fusedMap029 sourceMap029_checked fusedMap029_checked
    SmallGeFourComparisons.comparison029
#print axioms sourceMap029_checked
#print axioms fusedMap029_checked
#print axioms certified029
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
