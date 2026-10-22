/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5024 : Family 10 := level10.get ⟨1688,by decide⟩
def sourceMap5024 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,11,12,13,14,15,16,5,6,7,8,9,10] (sourceLabel 10 2 2 v)
def fusedMap5024 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5024_checked : acceptsGraphIso
    (source (graph core5024) (root 10) 2 2) DegreeTwoThreeSpectrum7625.graph sourceMap5024=true := by decide +kernel
theorem fusedMap5024_checked : acceptsGraphIso
    (fused (graph core5024) (root 10) 2 2) DegreeTwoThreeSpectrum6356.graph fusedMap5024=true := by decide +kernel
theorem certified5024 : Certified (graph core5024) (root 10) 2 2 :=
  of_native_maps core5024 DegreeTwoThreeSpectrum7625.graph DegreeTwoThreeSpectrum6356.graph
    sourceMap5024 fusedMap5024 sourceMap5024_checked fusedMap5024_checked
    DegreeTwoThreeFiniteComparisons.comparison5024
#print axioms sourceMap5024_checked
#print axioms fusedMap5024_checked
#print axioms certified5024
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
