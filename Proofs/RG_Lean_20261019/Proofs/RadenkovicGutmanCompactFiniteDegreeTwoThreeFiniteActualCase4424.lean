/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4424 : Family 9 := level9.get ⟨657,by decide⟩
def sourceMap4424 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4424 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4424_checked : acceptsGraphIso
    (source (graph core4424) (root 9) 2 2) DegreeTwoThreeSpectrum4951.graph sourceMap4424=true := by decide +kernel
theorem fusedMap4424_checked : acceptsGraphIso
    (fused (graph core4424) (root 9) 2 2) DegreeTwoThreeSpectrum4456.graph fusedMap4424=true := by decide +kernel
theorem certified4424 : Certified (graph core4424) (root 9) 2 2 :=
  of_native_maps core4424 DegreeTwoThreeSpectrum4951.graph DegreeTwoThreeSpectrum4456.graph
    sourceMap4424 fusedMap4424 sourceMap4424_checked fusedMap4424_checked
    DegreeTwoThreeFiniteComparisons.comparison4424
#print axioms sourceMap4424_checked
#print axioms fusedMap4424_checked
#print axioms certified4424
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
