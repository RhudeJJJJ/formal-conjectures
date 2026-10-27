/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4442 : Family 10 := level10.get ⟨66,by decide⟩
def sourceMap4442 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4442 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4442_checked : acceptsGraphIso
    (source (graph core4442) (root 10) 2 2) DegreeTwoThreeSpectrum6332.graph sourceMap4442=true := by decide +kernel
theorem fusedMap4442_checked : acceptsGraphIso
    (fused (graph core4442) (root 10) 2 2) DegreeTwoThreeSpectrum4979.graph fusedMap4442=true := by decide +kernel
theorem certified4442 : Certified (graph core4442) (root 10) 2 2 :=
  of_native_maps core4442 DegreeTwoThreeSpectrum6332.graph DegreeTwoThreeSpectrum4979.graph
    sourceMap4442 fusedMap4442 sourceMap4442_checked fusedMap4442_checked
    DegreeTwoThreeFiniteComparisons.comparison4442
#print axioms sourceMap4442_checked
#print axioms fusedMap4442_checked
#print axioms certified4442
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
