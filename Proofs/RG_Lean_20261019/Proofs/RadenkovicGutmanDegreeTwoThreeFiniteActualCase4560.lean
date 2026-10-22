/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4560 : Family 10 := level10.get ⟨478,by decide⟩
def sourceMap4560 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,10,11,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4560 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4560_checked : acceptsGraphIso
    (source (graph core4560) (root 10) 2 2) DegreeTwoThreeSpectrum6804.graph sourceMap4560=true := by decide +kernel
theorem fusedMap4560_checked : acceptsGraphIso
    (fused (graph core4560) (root 10) 2 2) DegreeTwoThreeSpectrum5942.graph fusedMap4560=true := by decide +kernel
theorem certified4560 : Certified (graph core4560) (root 10) 2 2 :=
  of_native_maps core4560 DegreeTwoThreeSpectrum6804.graph DegreeTwoThreeSpectrum5942.graph
    sourceMap4560 fusedMap4560 sourceMap4560_checked fusedMap4560_checked
    DegreeTwoThreeFiniteComparisons.comparison4560
#print axioms sourceMap4560_checked
#print axioms fusedMap4560_checked
#print axioms certified4560
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
