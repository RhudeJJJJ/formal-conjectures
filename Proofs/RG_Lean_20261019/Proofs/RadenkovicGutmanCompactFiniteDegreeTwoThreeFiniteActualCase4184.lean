/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4184 : Family 8 := level8.get ⟨244,by decide⟩
def sourceMap4184 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap4184 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4184_checked : acceptsGraphIso
    (source (graph core4184) (root 8) 2 2) DegreeTwoThreeSpectrum3843.graph sourceMap4184=true := by decide +kernel
theorem fusedMap4184_checked : acceptsGraphIso
    (fused (graph core4184) (root 8) 2 2) DegreeTwoThreeSpectrum2702.graph fusedMap4184=true := by decide +kernel
theorem certified4184 : Certified (graph core4184) (root 8) 2 2 :=
  of_native_maps core4184 DegreeTwoThreeSpectrum3843.graph DegreeTwoThreeSpectrum2702.graph
    sourceMap4184 fusedMap4184 sourceMap4184_checked fusedMap4184_checked
    DegreeTwoThreeFiniteComparisons.comparison4184
#print axioms sourceMap4184_checked
#print axioms fusedMap4184_checked
#print axioms certified4184
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
