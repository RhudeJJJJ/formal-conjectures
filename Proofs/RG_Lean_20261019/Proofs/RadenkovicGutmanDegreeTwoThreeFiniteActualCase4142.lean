/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4142 : Family 8 := level8.get ⟨152,by decide⟩
def sourceMap4142 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4142 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4142_checked : acceptsGraphIso
    (source (graph core4142) (root 8) 2 2) DegreeTwoThreeSpectrum3559.graph sourceMap4142=true := by decide +kernel
theorem fusedMap4142_checked : acceptsGraphIso
    (fused (graph core4142) (root 8) 2 2) DegreeTwoThreeSpectrum2744.graph fusedMap4142=true := by decide +kernel
theorem certified4142 : Certified (graph core4142) (root 8) 2 2 :=
  of_native_maps core4142 DegreeTwoThreeSpectrum3559.graph DegreeTwoThreeSpectrum2744.graph
    sourceMap4142 fusedMap4142 sourceMap4142_checked fusedMap4142_checked
    DegreeTwoThreeFiniteComparisons.comparison4142
#print axioms sourceMap4142_checked
#print axioms fusedMap4142_checked
#print axioms certified4142
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
