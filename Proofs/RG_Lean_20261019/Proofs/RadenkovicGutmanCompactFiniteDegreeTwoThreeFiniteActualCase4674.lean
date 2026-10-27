/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4674 : Family 10 := level10.get ⟨811,by decide⟩
def sourceMap4674 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,15,16,13,14,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4674 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4674_checked : acceptsGraphIso
    (source (graph core4674) (root 10) 2 2) DegreeTwoThreeSpectrum7468.graph sourceMap4674=true := by decide +kernel
theorem fusedMap4674_checked : acceptsGraphIso
    (fused (graph core4674) (root 10) 2 2) DegreeTwoThreeSpectrum5608.graph fusedMap4674=true := by decide +kernel
theorem certified4674 : Certified (graph core4674) (root 10) 2 2 :=
  of_native_maps core4674 DegreeTwoThreeSpectrum7468.graph DegreeTwoThreeSpectrum5608.graph
    sourceMap4674 fusedMap4674 sourceMap4674_checked fusedMap4674_checked
    DegreeTwoThreeFiniteComparisons.comparison4674
#print axioms sourceMap4674_checked
#print axioms fusedMap4674_checked
#print axioms certified4674
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
