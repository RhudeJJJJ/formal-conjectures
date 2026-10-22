/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4927 : Family 10 := level10.get ⟨1433,by decide⟩
def sourceMap4927 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,7,8,9,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap4927 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4927_checked : acceptsGraphIso
    (source (graph core4927) (root 10) 2 2) DegreeTwoThreeSpectrum7492.graph sourceMap4927=true := by decide +kernel
theorem fusedMap4927_checked : acceptsGraphIso
    (fused (graph core4927) (root 10) 2 2) DegreeTwoThreeSpectrum6892.graph fusedMap4927=true := by decide +kernel
theorem certified4927 : Certified (graph core4927) (root 10) 2 2 :=
  of_native_maps core4927 DegreeTwoThreeSpectrum7492.graph DegreeTwoThreeSpectrum6892.graph
    sourceMap4927 fusedMap4927 sourceMap4927_checked fusedMap4927_checked
    DegreeTwoThreeFiniteComparisons.comparison4927
#print axioms sourceMap4927_checked
#print axioms fusedMap4927_checked
#print axioms certified4927
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
