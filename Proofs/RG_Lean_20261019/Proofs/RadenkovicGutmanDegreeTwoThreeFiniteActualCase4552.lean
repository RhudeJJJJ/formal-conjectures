/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4552 : Family 10 := level10.get ⟨458,by decide⟩
def sourceMap4552 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,9,10,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4552 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4552_checked : acceptsGraphIso
    (source (graph core4552) (root 10) 2 2) DegreeTwoThreeSpectrum6823.graph sourceMap4552=true := by decide +kernel
theorem fusedMap4552_checked : acceptsGraphIso
    (fused (graph core4552) (root 10) 2 2) DegreeTwoThreeSpectrum5895.graph fusedMap4552=true := by decide +kernel
theorem certified4552 : Certified (graph core4552) (root 10) 2 2 :=
  of_native_maps core4552 DegreeTwoThreeSpectrum6823.graph DegreeTwoThreeSpectrum5895.graph
    sourceMap4552 fusedMap4552 sourceMap4552_checked fusedMap4552_checked
    DegreeTwoThreeFiniteComparisons.comparison4552
#print axioms sourceMap4552_checked
#print axioms fusedMap4552_checked
#print axioms certified4552
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
