/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons13
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core233 : Family 9 := level9.get ⟨704,by decide⟩
def sourceMap233 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap233 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap233_checked : acceptsGraphIso
    (source (graph core233) (root 9) 0 0) SmallGeFourSpectrum220.graph
      sourceMap233=true := by decide +kernel
theorem fusedMap233_checked : acceptsGraphIso
    (fused (graph core233) (root 9) 0 0) SmallGeFourSpectrum219.graph
      fusedMap233=true := by decide +kernel
theorem certified233 : Certified (graph core233) (root 9) 0 0 :=
  of_native_maps core233 SmallGeFourSpectrum220.graph SmallGeFourSpectrum219.graph
    sourceMap233 fusedMap233 sourceMap233_checked fusedMap233_checked
    SmallGeFourComparisons.comparison233
#print axioms sourceMap233_checked
#print axioms fusedMap233_checked
#print axioms certified233
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
