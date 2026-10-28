/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5043 : Family 10 := level10.get ⟨1744,by decide⟩
def sourceMap5043 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5043 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5043_checked : acceptsGraphIso
    (source (graph core5043) (root 10) 2 2) DegreeTwoThreeSpectrum7644.graph sourceMap5043=true := by decide +kernel
theorem fusedMap5043_checked : acceptsGraphIso
    (fused (graph core5043) (root 10) 2 2) DegreeTwoThreeSpectrum6597.graph fusedMap5043=true := by decide +kernel
theorem certified5043 : Certified (graph core5043) (root 10) 2 2 :=
  of_native_maps core5043 DegreeTwoThreeSpectrum7644.graph DegreeTwoThreeSpectrum6597.graph
    sourceMap5043 fusedMap5043 sourceMap5043_checked fusedMap5043_checked
    DegreeTwoThreeFiniteComparisons.comparison5043
#print axioms sourceMap5043_checked
#print axioms fusedMap5043_checked
#print axioms certified5043
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
