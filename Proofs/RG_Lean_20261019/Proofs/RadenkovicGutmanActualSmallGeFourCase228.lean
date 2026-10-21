/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons13
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core228 : Family 9 := level9.get ⟨688,by decide⟩
def sourceMap228 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,10,11,2,3,4,5,6,7,8,9] (sourceLabel 9 0 0 v)
def fusedMap228 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,9,10,11,3,4,5,6,7,8,1,2] (fusedLabel 9 0 0 v)
theorem sourceMap228_checked : acceptsGraphIso
    (source (graph core228) (root 9) 0 0) SmallGeFourSpectrum199.graph
      sourceMap228=true := by decide +kernel
theorem fusedMap228_checked : acceptsGraphIso
    (fused (graph core228) (root 9) 0 0) SmallGeFourSpectrum178.graph
      fusedMap228=true := by decide +kernel
theorem certified228 : Certified (graph core228) (root 9) 0 0 :=
  of_native_maps core228 SmallGeFourSpectrum199.graph SmallGeFourSpectrum178.graph
    sourceMap228 fusedMap228 sourceMap228_checked fusedMap228_checked
    SmallGeFourComparisons.comparison228
#print axioms sourceMap228_checked
#print axioms fusedMap228_checked
#print axioms certified228
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
