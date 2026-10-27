/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4148 : Family 8 := level8.get ⟨165,by decide⟩
def sourceMap4148 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,7,1,2,3,4,5,6] (sourceLabel 8 2 2 v)
def fusedMap4148 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4148_checked : acceptsGraphIso
    (source (graph core4148) (root 8) 2 2) DegreeTwoThreeSpectrum3622.graph sourceMap4148=true := by decide +kernel
theorem fusedMap4148_checked : acceptsGraphIso
    (fused (graph core4148) (root 8) 2 2) DegreeTwoThreeSpectrum2837.graph fusedMap4148=true := by decide +kernel
theorem certified4148 : Certified (graph core4148) (root 8) 2 2 :=
  of_native_maps core4148 DegreeTwoThreeSpectrum3622.graph DegreeTwoThreeSpectrum2837.graph
    sourceMap4148 fusedMap4148 sourceMap4148_checked fusedMap4148_checked
    DegreeTwoThreeFiniteComparisons.comparison4148
#print axioms sourceMap4148_checked
#print axioms fusedMap4148_checked
#print axioms certified4148
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
