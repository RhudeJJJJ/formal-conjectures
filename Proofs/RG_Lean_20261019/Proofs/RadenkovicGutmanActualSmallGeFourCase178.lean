/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons10
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core178 : Family 9 := level9.get ⟨385,by decide⟩
def sourceMap178 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap178 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap178_checked : acceptsGraphIso
    (source (graph core178) (root 9) 0 0) SmallGeFourSpectrum123.graph
      sourceMap178=true := by decide +kernel
theorem fusedMap178_checked : acceptsGraphIso
    (fused (graph core178) (root 9) 0 0) SmallGeFourSpectrum153.graph
      fusedMap178=true := by decide +kernel
theorem certified178 : Certified (graph core178) (root 9) 0 0 :=
  of_native_maps core178 SmallGeFourSpectrum123.graph SmallGeFourSpectrum153.graph
    sourceMap178 fusedMap178 sourceMap178_checked fusedMap178_checked
    SmallGeFourComparisons.comparison178
#print axioms sourceMap178_checked
#print axioms fusedMap178_checked
#print axioms certified178
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
