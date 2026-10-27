/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4558 : Family 10 := level10.get ⟨474,by decide⟩
def sourceMap4558 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,9,10,11,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4558 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4558_checked : acceptsGraphIso
    (source (graph core4558) (root 10) 2 2) DegreeTwoThreeSpectrum6820.graph sourceMap4558=true := by decide +kernel
theorem fusedMap4558_checked : acceptsGraphIso
    (fused (graph core4558) (root 10) 2 2) DegreeTwoThreeSpectrum5935.graph fusedMap4558=true := by decide +kernel
theorem certified4558 : Certified (graph core4558) (root 10) 2 2 :=
  of_native_maps core4558 DegreeTwoThreeSpectrum6820.graph DegreeTwoThreeSpectrum5935.graph
    sourceMap4558 fusedMap4558 sourceMap4558_checked fusedMap4558_checked
    DegreeTwoThreeFiniteComparisons.comparison4558
#print axioms sourceMap4558_checked
#print axioms fusedMap4558_checked
#print axioms certified4558
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
