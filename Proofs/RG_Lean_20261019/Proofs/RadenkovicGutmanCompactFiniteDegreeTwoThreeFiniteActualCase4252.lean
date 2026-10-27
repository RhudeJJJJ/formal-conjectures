/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4252 : Family 9 := level9.get ⟨223,by decide⟩
def sourceMap4252 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,15,14,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4252 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4252_checked : acceptsGraphIso
    (source (graph core4252) (root 9) 2 2) DegreeTwoThreeSpectrum4835.graph sourceMap4252=true := by decide +kernel
theorem fusedMap4252_checked : acceptsGraphIso
    (fused (graph core4252) (root 9) 2 2) DegreeTwoThreeSpectrum4011.graph fusedMap4252=true := by decide +kernel
theorem certified4252 : Certified (graph core4252) (root 9) 2 2 :=
  of_native_maps core4252 DegreeTwoThreeSpectrum4835.graph DegreeTwoThreeSpectrum4011.graph
    sourceMap4252 fusedMap4252 sourceMap4252_checked fusedMap4252_checked
    DegreeTwoThreeFiniteComparisons.comparison4252
#print axioms sourceMap4252_checked
#print axioms fusedMap4252_checked
#print axioms certified4252
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
