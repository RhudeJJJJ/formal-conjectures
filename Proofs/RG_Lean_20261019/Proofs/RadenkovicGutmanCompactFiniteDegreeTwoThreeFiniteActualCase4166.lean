/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4166 : Family 8 := level8.get ⟨204,by decide⟩
def sourceMap4166 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,12,13,14,6,7,8,9,10,11] (sourceLabel 8 2 2 v)
def fusedMap4166 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4166_checked : acceptsGraphIso
    (source (graph core4166) (root 8) 2 2) DegreeTwoThreeSpectrum3781.graph sourceMap4166=true := by decide +kernel
theorem fusedMap4166_checked : acceptsGraphIso
    (fused (graph core4166) (root 8) 2 2) DegreeTwoThreeSpectrum2474.graph fusedMap4166=true := by decide +kernel
theorem certified4166 : Certified (graph core4166) (root 8) 2 2 :=
  of_native_maps core4166 DegreeTwoThreeSpectrum3781.graph DegreeTwoThreeSpectrum2474.graph
    sourceMap4166 fusedMap4166 sourceMap4166_checked fusedMap4166_checked
    DegreeTwoThreeFiniteComparisons.comparison4166
#print axioms sourceMap4166_checked
#print axioms fusedMap4166_checked
#print axioms certified4166
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
