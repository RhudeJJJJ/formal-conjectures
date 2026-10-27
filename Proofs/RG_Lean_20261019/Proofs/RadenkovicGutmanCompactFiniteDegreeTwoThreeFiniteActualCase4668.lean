/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4668 : Family 10 := level10.get ⟨794,by decide⟩
def sourceMap4668 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,16,14,15,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4668 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4668_checked : acceptsGraphIso
    (source (graph core4668) (root 10) 2 2) DegreeTwoThreeSpectrum7459.graph sourceMap4668=true := by decide +kernel
theorem fusedMap4668_checked : acceptsGraphIso
    (fused (graph core4668) (root 10) 2 2) DegreeTwoThreeSpectrum5580.graph fusedMap4668=true := by decide +kernel
theorem certified4668 : Certified (graph core4668) (root 10) 2 2 :=
  of_native_maps core4668 DegreeTwoThreeSpectrum7459.graph DegreeTwoThreeSpectrum5580.graph
    sourceMap4668 fusedMap4668 sourceMap4668_checked fusedMap4668_checked
    DegreeTwoThreeFiniteComparisons.comparison4668
#print axioms sourceMap4668_checked
#print axioms fusedMap4668_checked
#print axioms certified4668
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
