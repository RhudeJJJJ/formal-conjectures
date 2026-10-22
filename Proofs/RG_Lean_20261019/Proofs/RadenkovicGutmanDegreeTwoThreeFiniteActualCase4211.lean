/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4211 : Family 9 := level9.get ⟨90,by decide⟩
def sourceMap4211 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,6,0,1,2,3,4,5,15,14,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4211 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4211_checked : acceptsGraphIso
    (source (graph core4211) (root 9) 2 2) DegreeTwoThreeSpectrum4534.graph sourceMap4211=true := by decide +kernel
theorem fusedMap4211_checked : acceptsGraphIso
    (fused (graph core4211) (root 9) 2 2) DegreeTwoThreeSpectrum4054.graph fusedMap4211=true := by decide +kernel
theorem certified4211 : Certified (graph core4211) (root 9) 2 2 :=
  of_native_maps core4211 DegreeTwoThreeSpectrum4534.graph DegreeTwoThreeSpectrum4054.graph
    sourceMap4211 fusedMap4211 sourceMap4211_checked fusedMap4211_checked
    DegreeTwoThreeFiniteComparisons.comparison4211
#print axioms sourceMap4211_checked
#print axioms fusedMap4211_checked
#print axioms certified4211
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
