/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons08
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core146 : Family 8 := level8.get ⟨270,by decide⟩
def sourceMap146 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,6,7,8,9,10,1,2,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap146 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,8,9,10,6,7] (fusedLabel 8 0 0 v)
theorem sourceMap146_checked : acceptsGraphIso
    (source (graph core146) (root 8) 0 0) SmallGeFourSpectrum075.graph
      sourceMap146=true := by decide +kernel
theorem fusedMap146_checked : acceptsGraphIso
    (fused (graph core146) (root 8) 0 0) SmallGeFourSpectrum080.graph
      fusedMap146=true := by decide +kernel
theorem certified146 : Certified (graph core146) (root 8) 0 0 :=
  of_native_maps core146 SmallGeFourSpectrum075.graph SmallGeFourSpectrum080.graph
    sourceMap146 fusedMap146 sourceMap146_checked fusedMap146_checked
    SmallGeFourComparisons.comparison146
#print axioms sourceMap146_checked
#print axioms fusedMap146_checked
#print axioms certified146
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
