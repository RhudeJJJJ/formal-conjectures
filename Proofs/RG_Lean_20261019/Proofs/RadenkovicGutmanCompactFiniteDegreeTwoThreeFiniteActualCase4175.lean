/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4175 : Family 8 := level8.get ⟨223,by decide⟩
def sourceMap4175 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap4175 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4175_checked : acceptsGraphIso
    (source (graph core4175) (root 8) 2 2) DegreeTwoThreeSpectrum3815.graph sourceMap4175=true := by decide +kernel
theorem fusedMap4175_checked : acceptsGraphIso
    (fused (graph core4175) (root 8) 2 2) DegreeTwoThreeSpectrum2562.graph fusedMap4175=true := by decide +kernel
theorem certified4175 : Certified (graph core4175) (root 8) 2 2 :=
  of_native_maps core4175 DegreeTwoThreeSpectrum3815.graph DegreeTwoThreeSpectrum2562.graph
    sourceMap4175 fusedMap4175 sourceMap4175_checked fusedMap4175_checked
    DegreeTwoThreeFiniteComparisons.comparison4175
#print axioms sourceMap4175_checked
#print axioms fusedMap4175_checked
#print axioms certified4175
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
