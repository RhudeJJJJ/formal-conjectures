/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4687 : Family 10 := level10.get ⟨846,by decide⟩
def sourceMap4687 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4687 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4687_checked : acceptsGraphIso
    (source (graph core4687) (root 10) 2 2) DegreeTwoThreeSpectrum7526.graph sourceMap4687=true := by decide +kernel
theorem fusedMap4687_checked : acceptsGraphIso
    (fused (graph core4687) (root 10) 2 2) DegreeTwoThreeSpectrum5678.graph fusedMap4687=true := by decide +kernel
theorem certified4687 : Certified (graph core4687) (root 10) 2 2 :=
  of_native_maps core4687 DegreeTwoThreeSpectrum7526.graph DegreeTwoThreeSpectrum5678.graph
    sourceMap4687 fusedMap4687 sourceMap4687_checked fusedMap4687_checked
    DegreeTwoThreeFiniteComparisons.comparison4687
#print axioms sourceMap4687_checked
#print axioms fusedMap4687_checked
#print axioms certified4687
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
