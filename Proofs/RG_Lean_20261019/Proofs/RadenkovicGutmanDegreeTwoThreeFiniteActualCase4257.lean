/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4257 : Family 9 := level9.get ⟨237,by decide⟩
def sourceMap4257 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4257 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4257_checked : acceptsGraphIso
    (source (graph core4257) (root 9) 2 2) DegreeTwoThreeSpectrum4853.graph sourceMap4257=true := by decide +kernel
theorem fusedMap4257_checked : acceptsGraphIso
    (fused (graph core4257) (root 9) 2 2) DegreeTwoThreeSpectrum4031.graph fusedMap4257=true := by decide +kernel
theorem certified4257 : Certified (graph core4257) (root 9) 2 2 :=
  of_native_maps core4257 DegreeTwoThreeSpectrum4853.graph DegreeTwoThreeSpectrum4031.graph
    sourceMap4257 fusedMap4257 sourceMap4257_checked fusedMap4257_checked
    DegreeTwoThreeFiniteComparisons.comparison4257
#print axioms sourceMap4257_checked
#print axioms fusedMap4257_checked
#print axioms certified4257
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
