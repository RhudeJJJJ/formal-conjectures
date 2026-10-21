/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons13
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core232 : Family 9 := level9.get ⟨703,by decide⟩
def sourceMap232 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap232 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap232_checked : acceptsGraphIso
    (source (graph core232) (root 9) 0 0) SmallGeFourSpectrum218.graph
      sourceMap232=true := by decide +kernel
theorem fusedMap232_checked : acceptsGraphIso
    (fused (graph core232) (root 9) 0 0) SmallGeFourSpectrum217.graph
      fusedMap232=true := by decide +kernel
theorem certified232 : Certified (graph core232) (root 9) 0 0 :=
  of_native_maps core232 SmallGeFourSpectrum218.graph SmallGeFourSpectrum217.graph
    sourceMap232 fusedMap232 sourceMap232_checked fusedMap232_checked
    SmallGeFourComparisons.comparison232
#print axioms sourceMap232_checked
#print axioms fusedMap232_checked
#print axioms certified232
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
