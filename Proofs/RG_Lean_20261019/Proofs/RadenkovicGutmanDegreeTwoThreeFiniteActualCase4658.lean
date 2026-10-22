/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4658 : Family 10 := level10.get ⟨766,by decide⟩
def sourceMap4658 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4658 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4658_checked : acceptsGraphIso
    (source (graph core4658) (root 10) 2 2) DegreeTwoThreeSpectrum7435.graph sourceMap4658=true := by decide +kernel
theorem fusedMap4658_checked : acceptsGraphIso
    (fused (graph core4658) (root 10) 2 2) DegreeTwoThreeSpectrum5543.graph fusedMap4658=true := by decide +kernel
theorem certified4658 : Certified (graph core4658) (root 10) 2 2 :=
  of_native_maps core4658 DegreeTwoThreeSpectrum7435.graph DegreeTwoThreeSpectrum5543.graph
    sourceMap4658 fusedMap4658 sourceMap4658_checked fusedMap4658_checked
    DegreeTwoThreeFiniteComparisons.comparison4658
#print axioms sourceMap4658_checked
#print axioms fusedMap4658_checked
#print axioms certified4658
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
