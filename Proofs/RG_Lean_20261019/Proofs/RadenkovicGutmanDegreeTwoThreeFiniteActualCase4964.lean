/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4964 : Family 10 := level10.get ⟨1536,by decide⟩
def sourceMap4964 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4964 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4964_checked : acceptsGraphIso
    (source (graph core4964) (root 10) 2 2) DegreeTwoThreeSpectrum7565.graph sourceMap4964=true := by decide +kernel
theorem fusedMap4964_checked : acceptsGraphIso
    (fused (graph core4964) (root 10) 2 2) DegreeTwoThreeSpectrum5977.graph fusedMap4964=true := by decide +kernel
theorem certified4964 : Certified (graph core4964) (root 10) 2 2 :=
  of_native_maps core4964 DegreeTwoThreeSpectrum7565.graph DegreeTwoThreeSpectrum5977.graph
    sourceMap4964 fusedMap4964 sourceMap4964_checked fusedMap4964_checked
    DegreeTwoThreeFiniteComparisons.comparison4964
#print axioms sourceMap4964_checked
#print axioms fusedMap4964_checked
#print axioms certified4964
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
