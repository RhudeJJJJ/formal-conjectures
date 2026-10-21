/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons09
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core162 : Family 8 := level8.get ⟨282,by decide⟩
def sourceMap162 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap162 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,9,10,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap162_checked : acceptsGraphIso
    (source (graph core162) (root 8) 0 0) SmallGeFourSpectrum090.graph
      sourceMap162=true := by decide +kernel
theorem fusedMap162_checked : acceptsGraphIso
    (fused (graph core162) (root 8) 0 0) SmallGeFourSpectrum089.graph
      fusedMap162=true := by decide +kernel
theorem certified162 : Certified (graph core162) (root 8) 0 0 :=
  of_native_maps core162 SmallGeFourSpectrum090.graph SmallGeFourSpectrum089.graph
    sourceMap162 fusedMap162 sourceMap162_checked fusedMap162_checked
    SmallGeFourComparisons.comparison162
#print axioms sourceMap162_checked
#print axioms fusedMap162_checked
#print axioms certified162
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
