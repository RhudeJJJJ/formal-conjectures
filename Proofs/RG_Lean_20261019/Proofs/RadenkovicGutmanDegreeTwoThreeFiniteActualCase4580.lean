/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4580 : Family 10 := level10.get ⟨541,by decide⟩
def sourceMap4580 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4580 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4580_checked : acceptsGraphIso
    (source (graph core4580) (root 10) 2 2) DegreeTwoThreeSpectrum7160.graph sourceMap4580=true := by decide +kernel
theorem fusedMap4580_checked : acceptsGraphIso
    (fused (graph core4580) (root 10) 2 2) DegreeTwoThreeSpectrum5190.graph fusedMap4580=true := by decide +kernel
theorem certified4580 : Certified (graph core4580) (root 10) 2 2 :=
  of_native_maps core4580 DegreeTwoThreeSpectrum7160.graph DegreeTwoThreeSpectrum5190.graph
    sourceMap4580 fusedMap4580 sourceMap4580_checked fusedMap4580_checked
    DegreeTwoThreeFiniteComparisons.comparison4580
#print axioms sourceMap4580_checked
#print axioms fusedMap4580_checked
#print axioms certified4580
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
