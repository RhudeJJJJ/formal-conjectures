/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4126 : Family 8 := level8.get ⟨106,by decide⟩
def sourceMap4126 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap4126 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4126_checked : acceptsGraphIso
    (source (graph core4126) (root 8) 2 2) DegreeTwoThreeSpectrum3145.graph sourceMap4126=true := by decide +kernel
theorem fusedMap4126_checked : acceptsGraphIso
    (fused (graph core4126) (root 8) 2 2) DegreeTwoThreeSpectrum2488.graph fusedMap4126=true := by decide +kernel
theorem certified4126 : Certified (graph core4126) (root 8) 2 2 :=
  of_native_maps core4126 DegreeTwoThreeSpectrum3145.graph DegreeTwoThreeSpectrum2488.graph
    sourceMap4126 fusedMap4126 sourceMap4126_checked fusedMap4126_checked
    DegreeTwoThreeFiniteComparisons.comparison4126
#print axioms sourceMap4126_checked
#print axioms fusedMap4126_checked
#print axioms certified4126
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
