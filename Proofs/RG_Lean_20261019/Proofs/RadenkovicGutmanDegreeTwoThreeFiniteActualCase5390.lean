/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5390 : Family 6 := level6.get ⟨28,by decide⟩
def sourceMap5390 : (Vertices 6 ⊕ Fin 5 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 4 4 v)
def fusedMap5390 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 4 4 v)
theorem sourceMap5390_checked : acceptsGraphIso
    (source (graph core5390) (root 6) 4 4) DegreeTwoThreeSpectrum7049.graph sourceMap5390=true := by decide +kernel
theorem fusedMap5390_checked : acceptsGraphIso
    (fused (graph core5390) (root 6) 4 4) DegreeTwoThreeSpectrum5009.graph fusedMap5390=true := by decide +kernel
theorem certified5390 : Certified (graph core5390) (root 6) 4 4 :=
  of_native_maps core5390 DegreeTwoThreeSpectrum7049.graph DegreeTwoThreeSpectrum5009.graph
    sourceMap5390 fusedMap5390 sourceMap5390_checked fusedMap5390_checked
    DegreeTwoThreeFiniteComparisons.comparison5390
#print axioms sourceMap5390_checked
#print axioms fusedMap5390_checked
#print axioms certified5390
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
