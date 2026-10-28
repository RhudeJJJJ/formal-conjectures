/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5019 : Family 10 := level10.get ⟨1664,by decide⟩
def sourceMap5019 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5019 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5019_checked : acceptsGraphIso
    (source (graph core5019) (root 10) 2 2) DegreeTwoThreeSpectrum7620.graph sourceMap5019=true := by decide +kernel
theorem fusedMap5019_checked : acceptsGraphIso
    (fused (graph core5019) (root 10) 2 2) DegreeTwoThreeSpectrum6281.graph fusedMap5019=true := by decide +kernel
theorem certified5019 : Certified (graph core5019) (root 10) 2 2 :=
  of_native_maps core5019 DegreeTwoThreeSpectrum7620.graph DegreeTwoThreeSpectrum6281.graph
    sourceMap5019 fusedMap5019 sourceMap5019_checked fusedMap5019_checked
    DegreeTwoThreeFiniteComparisons.comparison5019
#print axioms sourceMap5019_checked
#print axioms fusedMap5019_checked
#print axioms certified5019
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
