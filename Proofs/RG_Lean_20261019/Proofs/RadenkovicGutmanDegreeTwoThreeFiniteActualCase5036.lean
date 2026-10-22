/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5036 : Family 10 := level10.get ⟨1724,by decide⟩
def sourceMap5036 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5036 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5036_checked : acceptsGraphIso
    (source (graph core5036) (root 10) 2 2) DegreeTwoThreeSpectrum7637.graph sourceMap5036=true := by decide +kernel
theorem fusedMap5036_checked : acceptsGraphIso
    (fused (graph core5036) (root 10) 2 2) DegreeTwoThreeSpectrum6526.graph fusedMap5036=true := by decide +kernel
theorem certified5036 : Certified (graph core5036) (root 10) 2 2 :=
  of_native_maps core5036 DegreeTwoThreeSpectrum7637.graph DegreeTwoThreeSpectrum6526.graph
    sourceMap5036 fusedMap5036 sourceMap5036_checked fusedMap5036_checked
    DegreeTwoThreeFiniteComparisons.comparison5036
#print axioms sourceMap5036_checked
#print axioms fusedMap5036_checked
#print axioms certified5036
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
