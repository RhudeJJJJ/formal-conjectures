/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4326 : Family 9 := level9.get ⟨420,by decide⟩
def sourceMap4326 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4326 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4326_checked : acceptsGraphIso
    (source (graph core4326) (root 9) 2 2) DegreeTwoThreeSpectrum4794.graph sourceMap4326=true := by decide +kernel
theorem fusedMap4326_checked : acceptsGraphIso
    (fused (graph core4326) (root 9) 2 2) DegreeTwoThreeSpectrum4402.graph fusedMap4326=true := by decide +kernel
theorem certified4326 : Certified (graph core4326) (root 9) 2 2 :=
  of_native_maps core4326 DegreeTwoThreeSpectrum4794.graph DegreeTwoThreeSpectrum4402.graph
    sourceMap4326 fusedMap4326 sourceMap4326_checked fusedMap4326_checked
    DegreeTwoThreeFiniteComparisons.comparison4326
#print axioms sourceMap4326_checked
#print axioms fusedMap4326_checked
#print axioms certified4326
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
