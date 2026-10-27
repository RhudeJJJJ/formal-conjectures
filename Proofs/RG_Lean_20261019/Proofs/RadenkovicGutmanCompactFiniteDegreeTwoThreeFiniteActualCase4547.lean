/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4547 : Family 10 := level10.get ⟨444,by decide⟩
def sourceMap4547 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,9,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4547 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4547_checked : acceptsGraphIso
    (source (graph core4547) (root 10) 2 2) DegreeTwoThreeSpectrum6833.graph sourceMap4547=true := by decide +kernel
theorem fusedMap4547_checked : acceptsGraphIso
    (fused (graph core4547) (root 10) 2 2) DegreeTwoThreeSpectrum5863.graph fusedMap4547=true := by decide +kernel
theorem certified4547 : Certified (graph core4547) (root 10) 2 2 :=
  of_native_maps core4547 DegreeTwoThreeSpectrum6833.graph DegreeTwoThreeSpectrum5863.graph
    sourceMap4547 fusedMap4547 sourceMap4547_checked fusedMap4547_checked
    DegreeTwoThreeFiniteComparisons.comparison4547
#print axioms sourceMap4547_checked
#print axioms fusedMap4547_checked
#print axioms certified4547
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
