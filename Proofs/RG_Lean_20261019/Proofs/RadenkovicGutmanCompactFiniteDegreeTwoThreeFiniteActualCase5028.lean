/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5028 : Family 10 := level10.get ⟨1705,by decide⟩
def sourceMap5028 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5028 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5028_checked : acceptsGraphIso
    (source (graph core5028) (root 10) 2 2) DegreeTwoThreeSpectrum7629.graph sourceMap5028=true := by decide +kernel
theorem fusedMap5028_checked : acceptsGraphIso
    (fused (graph core5028) (root 10) 2 2) DegreeTwoThreeSpectrum6475.graph fusedMap5028=true := by decide +kernel
theorem certified5028 : Certified (graph core5028) (root 10) 2 2 :=
  of_native_maps core5028 DegreeTwoThreeSpectrum7629.graph DegreeTwoThreeSpectrum6475.graph
    sourceMap5028 fusedMap5028 sourceMap5028_checked fusedMap5028_checked
    DegreeTwoThreeFiniteComparisons.comparison5028
#print axioms sourceMap5028_checked
#print axioms fusedMap5028_checked
#print axioms certified5028
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
